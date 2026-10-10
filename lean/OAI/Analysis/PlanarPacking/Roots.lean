import OAI.Analysis.PlanarPacking.Intervals
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Complex

namespace OAI

/-!
# Certified roots of unity

Integer enclosures for the 1024th roots of unity, obtained from a certified
Taylor approximation and repeated squaring.
-/

namespace SharpPlanar
noncomputable def rootPhase (n : ℕ) : ℂ := Complex.exp (Complex.I*Real.pi*((n:ℂ)/512))

lemma rootPhase_eq_pow (n : ℕ) : rootPhase n = rootPhase 1 ^ n := by
  rw [rootPhase,rootPhase,← Complex.exp_nat_mul]
  congr 1
  push_cast
  ring

lemma rootPhase_add (n m : ℕ) : rootPhase (n+m) = rootPhase n*rootPhase m := by
  unfold rootPhase
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

lemma rootPhase_periodic (n : ℕ) : rootPhase (n+1024) = rootPhase n := by
  unfold rootPhase
  have heq : Complex.I*Real.pi*(((n+1024:ℕ):ℂ)/512) =
    Complex.I*Real.pi*((n:ℂ)/512)+(2*Real.pi*Complex.I) := by push_cast; ring
  rw [heq,Complex.exp_add,Complex.exp_two_pi_mul_I,mul_one]

lemma rootPhase_mod (n : ℕ) : rootPhase (n%1024) = rootPhase n := by
  have hp : Function.Periodic rootPhase 1024 := rootPhase_periodic
  exact hp.map_mod_nat n

lemma rootPhase_cos (n : ℕ) : (rootPhase n).re = Real.cos (Real.pi*((n:ℝ)/512)) := by
  unfold rootPhase
  rw [Complex.exp_re]
  simp only [Complex.mul_re,Complex.mul_im,Complex.div_ofNat_re,Complex.div_ofNat_im,
    Complex.I_re,Complex.I_im,Complex.ofReal_re,Complex.ofReal_im,Complex.natCast_re,
    Complex.natCast_im,zero_mul,mul_zero,sub_zero,zero_add,one_mul,
    zero_div,Real.exp_zero]


end SharpPlanar

namespace SharpPlanar
namespace IntegerRoots
open IntegerIntervals
def fact0 : CBox := ⟨⟨1000000000000000000000000000000,1000000000000000000000000000000⟩,⟨0,0⟩⟩
lemma fact0_check : fact0.RatCheck 1 1 0 1 := by decide +kernel
def fact1 : CBox := ⟨⟨1000000000000000000000000000000,1000000000000000000000000000000⟩,⟨0,0⟩⟩
lemma fact1_check : fact1.RatCheck 1 1 0 1 := by decide +kernel
def fact2 : CBox := ⟨⟨500000000000000000000000000000,500000000000000000000000000000⟩,⟨0,0⟩⟩
lemma fact2_check : fact2.RatCheck 1 2 0 1 := by decide +kernel
def fact3 : CBox := ⟨⟨166666666666666666666666666666,166666666666666666666666666667⟩,⟨0,0⟩⟩
lemma fact3_check : fact3.RatCheck 1 6 0 1 := by decide +kernel
def fact4 : CBox := ⟨⟨41666666666666666666666666666,41666666666666666666666666667⟩,⟨0,0⟩⟩
lemma fact4_check : fact4.RatCheck 1 24 0 1 := by decide +kernel
def fact5 : CBox := ⟨⟨8333333333333333333333333333,8333333333333333333333333334⟩,⟨0,0⟩⟩
lemma fact5_check : fact5.RatCheck 1 120 0 1 := by decide +kernel
def fact6 : CBox := ⟨⟨1388888888888888888888888888,1388888888888888888888888889⟩,⟨0,0⟩⟩
lemma fact6_check : fact6.RatCheck 1 720 0 1 := by decide +kernel
def fact7 : CBox := ⟨⟨198412698412698412698412698,198412698412698412698412699⟩,⟨0,0⟩⟩
lemma fact7_check : fact7.RatCheck 1 5040 0 1 := by decide +kernel
def fact8 : CBox := ⟨⟨24801587301587301587301587,24801587301587301587301588⟩,⟨0,0⟩⟩
lemma fact8_check : fact8.RatCheck 1 40320 0 1 := by decide +kernel
def fact9 : CBox := ⟨⟨2755731922398589065255731,2755731922398589065255732⟩,⟨0,0⟩⟩
lemma fact9_check : fact9.RatCheck 1 362880 0 1 := by decide +kernel
def fact10 : CBox := ⟨⟨275573192239858906525573,275573192239858906525574⟩,⟨0,0⟩⟩
lemma fact10_check : fact10.RatCheck 1 3628800 0 1 := by decide +kernel
def fact11 : CBox := ⟨⟨25052108385441718775052,25052108385441718775053⟩,⟨0,0⟩⟩
lemma fact11_check : fact11.RatCheck 1 39916800 0 1 := by decide +kernel
def fact12 : CBox := ⟨⟨2087675698786809897921,2087675698786809897922⟩,⟨0,0⟩⟩
lemma fact12_check : fact12.RatCheck 1 479001600 0 1 := by decide +kernel
def fact13 : CBox := ⟨⟨160590438368216145993,160590438368216145994⟩,⟨0,0⟩⟩
lemma fact13_check : fact13.RatCheck 1 6227020800 0 1 := by decide +kernel
def fact14 : CBox := ⟨⟨11470745597729724713,11470745597729724714⟩,⟨0,0⟩⟩
lemma fact14_check : fact14.RatCheck 1 87178291200 0 1 := by decide +kernel
def fact15 : CBox := ⟨⟨764716373181981647,764716373181981648⟩,⟨0,0⟩⟩
lemma fact15_check : fact15.RatCheck 1 1307674368000 0 1 := by decide +kernel
def fact16 : CBox := ⟨⟨47794773323873852,47794773323873853⟩,⟨0,0⟩⟩
lemma fact16_check : fact16.RatCheck 1 20922789888000 0 1 := by decide +kernel
def fact17 : CBox := ⟨⟨2811457254345520,2811457254345521⟩,⟨0,0⟩⟩
lemma fact17_check : fact17.RatCheck 1 355687428096000 0 1 := by decide +kernel
def fact18 : CBox := ⟨⟨156192069685862,156192069685863⟩,⟨0,0⟩⟩
lemma fact18_check : fact18.RatCheck 1 6402373705728000 0 1 := by decide +kernel
def fact19 : CBox := ⟨⟨8220635246624,8220635246625⟩,⟨0,0⟩⟩
lemma fact19_check : fact19.RatCheck 1 121645100408832000 0 1 := by decide +kernel
def fact20 : CBox := ⟨⟨411031762331,411031762332⟩,⟨0,0⟩⟩
lemma fact20_check : fact20.RatCheck 1 2432902008176640000 0 1 := by decide +kernel
def fact21 : CBox := ⟨⟨19572941063,19572941064⟩,⟨0,0⟩⟩
lemma fact21_check : fact21.RatCheck 1 51090942171709440000 0 1 := by decide +kernel
def fact22 : CBox := ⟨⟨889679139,889679140⟩,⟨0,0⟩⟩
lemma fact22_check : fact22.RatCheck 1 1124000727777607680000 0 1 := by decide +kernel
def fact23 : CBox := ⟨⟨38681701,38681702⟩,⟨0,0⟩⟩
lemma fact23_check : fact23.RatCheck 1 25852016738884976640000 0 1 := by decide +kernel
def fact24 : CBox := ⟨⟨1611737,1611738⟩,⟨0,0⟩⟩
lemma fact24_check : fact24.RatCheck 1 620448401733239439360000 0 1 := by decide +kernel
def fact25 : CBox := ⟨⟨64469,64470⟩,⟨0,0⟩⟩
lemma fact25_check : fact25.RatCheck 1 15511210043330985984000000 0 1 := by decide +kernel
def fact26 : CBox := ⟨⟨2479,2480⟩,⟨0,0⟩⟩
lemma fact26_check : fact26.RatCheck 1 403291461126605635584000000 0 1 := by decide +kernel
def fact27 : CBox := ⟨⟨91,92⟩,⟨0,0⟩⟩
lemma fact27_check : fact27.RatCheck 1 10888869450418352160768000000 0 1 := by decide +kernel
def fact28 : CBox := ⟨⟨3,4⟩,⟨0,0⟩⟩
lemma fact28_check : fact28.RatCheck 1 304888344611713860501504000000 0 1 := by decide +kernel
def fact29 : CBox := ⟨⟨0,1⟩,⟨0,0⟩⟩
lemma fact29_check : fact29.RatCheck 1 8841761993739701954543616000000 0 1 := by decide +kernel
def fact30 : CBox := ⟨⟨0,1⟩,⟨0,0⟩⟩
lemma fact30_check : fact30.RatCheck 1 265252859812191058636308480000000 0 1 := by decide +kernel
def fact31 : CBox := ⟨⟨0,1⟩,⟨0,0⟩⟩
lemma fact31_check : fact31.RatCheck 1 8222838654177922817725562880000000 0 1 := by decide +kernel
def fact32 : CBox := ⟨⟨0,1⟩,⟨0,0⟩⟩
lemma fact32_check : fact32.RatCheck 1 263130836933693530167218012160000000 0 1 := by decide +kernel
def phaseInput : CBox := ⟨⟨0,0⟩,⟨6135923151542564918867187500,6135923151542564918886718750⟩⟩
lemma phaseInput_contains : phaseInput.Contains (Complex.I*Real.pi/512) := by
  constructor
  · norm_num [phaseInput,RBox.Contains,Complex.mul_re,Complex.I_re,Complex.I_im]
  · have hh := RBox.scale_contains piBounds_contains
      (c:=phaseInput.im) (m:=1) (n:=512) (by decide +kernel)
    simpa [div_eq_mul_inv,mul_comm] using hh
def small : CBox := ⟨⟨0,0⟩,⟨2996056226339143026790618,2996056226339143026800156⟩⟩
lemma small_contains : small.Contains ((1/2048:ℂ)*(Complex.I*Real.pi/512)) := by
  simpa using CBox.scale_contains phaseInput_contains (c:=small) (m:=1) (n:=2048) (by decide +kernel)
def poly32 : CBox := fact32
lemma h32 : poly32.Contains (expHorner ((1/2048:ℂ)*(Complex.I*Real.pi/512)) 32 0) := by
  simpa [expHorner,poly32,Nat.factorial] using CBox.rat_contains fact32_check
def mul31 : CBox := ⟨⟨0,0⟩,⟨0,1⟩⟩
def poly31 : CBox := ⟨⟨0,1⟩,⟨0,1⟩⟩
lemma h31 : poly31.Contains (expHorner ((1/2048:ℂ)*(Complex.I*Real.pi/512)) 31 1) := by
  exact horner_step small_contains h32 fact31_check (m:=mul31) (by decide +kernel) (by decide +kernel)
def mul30 : CBox := ⟨⟨(-1),0⟩,⟨0,1⟩⟩
def poly30 : CBox := ⟨⟨(-1),1⟩,⟨0,1⟩⟩
lemma h30 : poly30.Contains (expHorner ((1/2048:ℂ)*(Complex.I*Real.pi/512)) 30 2) := by
  exact horner_step small_contains h31 fact30_check (m:=mul30) (by decide +kernel) (by decide +kernel)
def mul29 : CBox := ⟨⟨(-1),0⟩,⟨(-1),1⟩⟩
def poly29 : CBox := ⟨⟨(-1),1⟩,⟨(-1),1⟩⟩
lemma h29 : poly29.Contains (expHorner ((1/2048:ℂ)*(Complex.I*Real.pi/512)) 29 3) := by
  exact horner_step small_contains h30 fact29_check (m:=mul29) (by decide +kernel) (by decide +kernel)
def mul28 : CBox := ⟨⟨(-1),1⟩,⟨(-1),1⟩⟩
def poly28 : CBox := ⟨⟨2,5⟩,⟨(-1),1⟩⟩
lemma h28 : poly28.Contains (expHorner ((1/2048:ℂ)*(Complex.I*Real.pi/512)) 28 4) := by
  exact horner_step small_contains h29 fact28_check (m:=mul28) (by decide +kernel) (by decide +kernel)
def mul27 : CBox := ⟨⟨(-1),1⟩,⟨0,1⟩⟩
def poly27 : CBox := ⟨⟨90,93⟩,⟨0,1⟩⟩
lemma h27 : poly27.Contains (expHorner ((1/2048:ℂ)*(Complex.I*Real.pi/512)) 27 5) := by
  exact horner_step small_contains h28 fact27_check (m:=mul27) (by decide +kernel) (by decide +kernel)
def mul26 : CBox := ⟨⟨(-1),0⟩,⟨0,1⟩⟩
def poly26 : CBox := ⟨⟨2478,2480⟩,⟨0,1⟩⟩
lemma h26 : poly26.Contains (expHorner ((1/2048:ℂ)*(Complex.I*Real.pi/512)) 26 6) := by
  exact horner_step small_contains h27 fact26_check (m:=mul26) (by decide +kernel) (by decide +kernel)
def mul25 : CBox := ⟨⟨(-1),0⟩,⟨0,1⟩⟩
def poly25 : CBox := ⟨⟨64468,64470⟩,⟨0,1⟩⟩
lemma h25 : poly25.Contains (expHorner ((1/2048:ℂ)*(Complex.I*Real.pi/512)) 25 7) := by
  exact horner_step small_contains h26 fact25_check (m:=mul25) (by decide +kernel) (by decide +kernel)
def mul24 : CBox := ⟨⟨(-1),0⟩,⟨0,1⟩⟩
def poly24 : CBox := ⟨⟨1611736,1611738⟩,⟨0,1⟩⟩
lemma h24 : poly24.Contains (expHorner ((1/2048:ℂ)*(Complex.I*Real.pi/512)) 24 8) := by
  exact horner_step small_contains h25 fact24_check (m:=mul24) (by decide +kernel) (by decide +kernel)
def mul23 : CBox := ⟨⟨(-1),0⟩,⟨4,5⟩⟩
def poly23 : CBox := ⟨⟨38681700,38681702⟩,⟨4,5⟩⟩
lemma h23 : poly23.Contains (expHorner ((1/2048:ℂ)*(Complex.I*Real.pi/512)) 23 9) := by
  exact horner_step small_contains h24 fact23_check (m:=mul23) (by decide +kernel) (by decide +kernel)
def mul22 : CBox := ⟨⟨(-1),0⟩,⟨115,116⟩⟩
def poly22 : CBox := ⟨⟨889679138,889679140⟩,⟨115,116⟩⟩
lemma h22 : poly22.Contains (expHorner ((1/2048:ℂ)*(Complex.I*Real.pi/512)) 22 10) := by
  exact horner_step small_contains h23 fact22_check (m:=mul22) (by decide +kernel) (by decide +kernel)
def mul21 : CBox := ⟨⟨(-1),0⟩,⟨2665,2666⟩⟩
def poly21 : CBox := ⟨⟨19572941062,19572941064⟩,⟨2665,2666⟩⟩
lemma h21 : poly21.Contains (expHorner ((1/2048:ℂ)*(Complex.I*Real.pi/512)) 21 11) := by
  exact horner_step small_contains h22 fact21_check (m:=mul21) (by decide +kernel) (by decide +kernel)
def mul20 : CBox := ⟨⟨(-1),0⟩,⟨58641,58642⟩⟩
def poly20 : CBox := ⟨⟨411031762330,411031762332⟩,⟨58641,58642⟩⟩
lemma h20 : poly20.Contains (expHorner ((1/2048:ℂ)*(Complex.I*Real.pi/512)) 20 12) := by
  exact horner_step small_contains h21 fact20_check (m:=mul20) (by decide +kernel) (by decide +kernel)
def mul19 : CBox := ⟨⟨(-1),0⟩,⟨1231474,1231475⟩⟩
def poly19 : CBox := ⟨⟨8220635246623,8220635246625⟩,⟨1231474,1231475⟩⟩
lemma h19 : poly19.Contains (expHorner ((1/2048:ℂ)*(Complex.I*Real.pi/512)) 19 13) := by
  exact horner_step small_contains h20 fact19_check (m:=mul19) (by decide +kernel) (by decide +kernel)
def mul18 : CBox := ⟨⟨(-4),(-3)⟩,⟨24629485,24629486⟩⟩
def poly18 : CBox := ⟨⟨156192069685858,156192069685860⟩,⟨24629485,24629486⟩⟩
lemma h18 : poly18.Contains (expHorner ((1/2048:ℂ)*(Complex.I*Real.pi/512)) 18 14) := by
  exact horner_step small_contains h19 fact18_check (m:=mul18) (by decide +kernel) (by decide +kernel)
def mul17 : CBox := ⟨⟨(-74),(-73)⟩,⟨467960222,467960223⟩⟩
def poly17 : CBox := ⟨⟨2811457254345446,2811457254345448⟩,⟨467960222,467960223⟩⟩
lemma h17 : poly17.Contains (expHorner ((1/2048:ℂ)*(Complex.I*Real.pi/512)) 17 15) := by
  exact horner_step small_contains h18 fact17_check (m:=mul17) (by decide +kernel) (by decide +kernel)
def mul16 : CBox := ⟨⟨(-1403),(-1402)⟩,⟨8423284011,8423284012⟩⟩
def poly16 : CBox := ⟨⟨47794773323872449,47794773323872451⟩,⟨8423284011,8423284012⟩⟩
lemma h16 : poly16.Contains (expHorner ((1/2048:ℂ)*(Complex.I*Real.pi/512)) 16 16) := by
  exact horner_step small_contains h17 fact16_check (m:=mul16) (by decide +kernel) (by decide +kernel)
def mul15 : CBox := ⟨⟨(-25237),(-25236)⟩,⟨143195828203,143195828204⟩⟩
def poly15 : CBox := ⟨⟨764716373181956410,764716373181956412⟩,⟨143195828203,143195828204⟩⟩
lemma h15 : poly15.Contains (expHorner ((1/2048:ℂ)*(Complex.I*Real.pi/512)) 15 17) := by
  exact horner_step small_contains h16 fact15_check (m:=mul15) (by decide +kernel) (by decide +kernel)
def mul14 : CBox := ⟨⟨(-429023),(-429022)⟩,⟨2291133251255,2291133251256⟩⟩
def poly14 : CBox := ⟨⟨11470745597729295690,11470745597729295692⟩,⟨2291133251255,2291133251256⟩⟩
lemma h14 : poly14.Contains (expHorner ((1/2048:ℂ)*(Complex.I*Real.pi/512)) 14 18) := by
  exact horner_step small_contains h15 fact14_check (m:=mul14) (by decide +kernel) (by decide +kernel)
def mul13 : CBox := ⟨⟨(-6864365),(-6864364)⟩,⟨34366998768829,34366998768830⟩⟩
def poly13 : CBox := ⟨⟨160590438368209281628,160590438368209281630⟩,⟨34366998768829,34366998768830⟩⟩
lemma h13 : poly13.Contains (expHorner ((1/2048:ℂ)*(Complex.I*Real.pi/512)) 13 19) := by
  exact horner_step small_contains h14 fact13_check (m:=mul13) (by decide +kernel) (by decide +kernel)
def mul12 : CBox := ⟨⟨(-102965461),(-102965460)⟩,⟨481137982763605,481137982763606⟩⟩
def poly12 : CBox := ⟨⟨2087675698786706932460,2087675698786706932462⟩,⟨481137982763605,481137982763606⟩⟩
lemma h12 : poly12.Contains (expHorner ((1/2048:ℂ)*(Complex.I*Real.pi/512)) 12 20) := by
  exact horner_step small_contains h13 fact12_check (m:=mul12) (by decide +kernel) (by decide +kernel)
def mul11 : CBox := ⟨⟨(-1441516449),(-1441516448)⟩,⟨6254793775926834,6254793775926835⟩⟩
def poly11 : CBox := ⟨⟨25052108385440277258603,25052108385440277258605⟩,⟨6254793775926834,6254793775926835⟩⟩
lemma h11 : poly11.Contains (expHorner ((1/2048:ℂ)*(Complex.I*Real.pi/512)) 11 21) := by
  exact horner_step small_contains h12 fact11_check (m:=mul11) (by decide +kernel) (by decide +kernel)
def mul10 : CBox := ⟨⟨(-18739713837),(-18739713836)⟩,⟨75057525311121398,75057525311121399⟩⟩
def poly10 : CBox := ⟨⟨275573192239840166811736,275573192239840166811738⟩,⟨75057525311121398,75057525311121399⟩⟩
lemma h10 : poly10.Contains (expHorner ((1/2048:ℂ)*(Complex.I*Real.pi/512)) 10 22) := by
  exact horner_step small_contains h11 fact10_check (m:=mul10) (by decide +kernel) (by decide +kernel)
def mul9 : CBox := ⟨⟨(-224876566042),(-224876566041)⟩,⟨825632778422326743,825632778422326744⟩⟩
def poly9 : CBox := ⟨⟨2755731922398364188689689,2755731922398364188689691⟩,⟨825632778422326743,825632778422326744⟩⟩
lemma h9 : poly9.Contains (expHorner ((1/2048:ℂ)*(Complex.I*Real.pi/512)) 9 23) := by
  exact horner_step small_contains h10 fact9_check (m:=mul9) (by decide +kernel) (by decide +kernel)
def mul8 : CBox := ⟨⟨(-2473642226462),(-2473642226461)⟩,⟨8256327784223155144,8256327784223155145⟩⟩
def poly8 : CBox := ⟨⟨24801587301584827945075125,24801587301584827945075127⟩,⟨8256327784223155144,8256327784223155145⟩⟩
lemma h8 : poly8.Contains (expHorner ((1/2048:ℂ)*(Complex.I*Real.pi/512)) 8 24) := by
  exact horner_step small_contains h9 fact8_check (m:=mul8) (by decide +kernel) (by decide +kernel)
def mul7 : CBox := ⟨⟨(-24736422264619),(-24736422264618)⟩,⟨74306950058007048818,74306950058007048819⟩⟩
def poly7 : CBox := ⟨⟨198412698412673676276148079,198412698412673676276148081⟩,⟨74306950058007048818,74306950058007048819⟩⟩
lemma h7 : poly7.Contains (expHorner ((1/2048:ℂ)*(Complex.I*Real.pi/512)) 7 25) := by
  exact horner_step small_contains h8 fact7_check (m:=mul7) (by decide +kernel) (by decide +kernel)
def mul6 : CBox := ⟨⟨(-222627800381564),(-222627800381563)⟩,⟨594455600464041568206,594455600464041568209⟩⟩
def poly6 : CBox := ⟨⟨1388888888888666261088507324,1388888888888666261088507326⟩,⟨594455600464041568206,594455600464041568209⟩⟩
lemma h6 : poly6.Contains (expHorner ((1/2048:ℂ)*(Complex.I*Real.pi/512)) 6 26) := by
  exact horner_step small_contains h7 fact6_check (m:=mul6) (by decide +kernel) (by decide +kernel)
def mul5 : CBox := ⟨⟨(-1781022403052466),(-1781022403052465)⟩,⟨4161189203248142754023,4161189203248142754038⟩⟩
def poly5 : CBox := ⟨⟨8333333333331552310930280867,8333333333331552310930280869⟩,⟨4161189203248142754023,4161189203248142754038⟩⟩
lemma h5 : poly5.Contains (expHorner ((1/2048:ℂ)*(Complex.I*Real.pi/512)) 5 27) := by
  exact horner_step small_contains h6 fact5_check (m:=mul5) (by decide +kernel) (by decide +kernel)
def mul4 : CBox := ⟨⟨(-12467156821366816),(-12467156821366815)⟩,⟨24967135219487522513328,24967135219487522513409⟩⟩
def poly4 : CBox := ⟨⟨41666666666654199509845299850,41666666666654199509845299852⟩,⟨24967135219487522513328,24967135219487522513409⟩⟩
lemma h4 : poly4.Contains (expHorner ((1/2048:ℂ)*(Complex.I*Real.pi/512)) 4 28) := by
  exact horner_step small_contains h5 fact4_check (m:=mul4) (by decide +kernel) (by decide +kernel)
def mul3 : CBox := ⟨⟨(-74802940928196899),(-74802940928196898)⟩,⟨124835676097426940480123,124835676097426940480521⟩⟩
def poly3 : CBox := ⟨⟨166666666666591863725738469767,166666666666591863725738469769⟩,⟨124835676097426940480123,124835676097426940480521⟩⟩
lemma h3 : poly3.Contains (expHorner ((1/2048:ℂ)*(Complex.I*Real.pi/512)) 3 29) := by
  exact horner_step small_contains h4 fact3_check (m:=mul3) (by decide +kernel) (by decide +kernel)
def mul2 : CBox := ⟨⟨(-374014704640952517),(-374014704640952516)⟩,⟨499342704389633057314853,499342704389633057316443⟩⟩
def poly2 : CBox := ⟨⟨499999999999625985295359047483,499999999999625985295359047484⟩,⟨499342704389633057314853,499342704389633057316443⟩⟩
lemma h2 : poly2.Contains (expHorner ((1/2048:ℂ)*(Complex.I*Real.pi/512)) 2 30) := by
  exact horner_step small_contains h3 fact2_check (m:=mul2) (by decide +kernel) (by decide +kernel)
def mul1 : CBox := ⟨⟨(-1496058818563586248),(-1496058818563586247)⟩,⟨1498028113168450944310727,1498028113168450944315497⟩⟩
def poly1 : CBox := ⟨⟨999999999998503941181436413752,999999999998503941181436413753⟩,⟨1498028113168450944310727,1498028113168450944315497⟩⟩
lemma h1 : poly1.Contains (expHorner ((1/2048:ℂ)*(Complex.I*Real.pi/512)) 1 31) := by
  exact horner_step small_contains h2 fact1_check (m:=mul1) (by decide +kernel) (by decide +kernel)
def mul0 : CBox := ⟨⟨(-4488176455689415828),(-4488176455689415826)⟩,⟨2996056226334660750452290,2996056226334660750461829⟩⟩
def poly0 : CBox := ⟨⟨999999999995511823544310584172,999999999995511823544310584174⟩,⟨2996056226334660750452290,2996056226334660750461829⟩⟩
lemma h0 : poly0.Contains (expHorner ((1/2048:ℂ)*(Complex.I*Real.pi/512)) 0 32) := by
  exact horner_step small_contains h1 fact0_check (m:=mul0) (by decide +kernel) (by decide +kernel)
def sq0 : CBox := ⟨⟨999999999995511823544310584171,999999999995511823544310584175⟩,⟨2996056226334660750452289,2996056226334660750461830⟩⟩
lemma sq0_contains : sq0.Contains (Complex.exp ((1/2048:ℂ)*(Complex.I*Real.pi/512)) ^ (2^0)) := by
  simpa using exp_from_horner small_contains (b:=poly0) (c:=sq0) (by decide +kernel) h0 (by decide +kernel)
def sq1 : CBox := ⟨⟨999999999982047294177282624143,999999999982047294177282624152⟩,⟨5992112452642427842874664,5992112452642427842893747⟩⟩
lemma sq1_contains : sq1.Contains (Complex.exp ((1/2048:ℂ)*(Complex.I*Real.pi/512)) ^ (2^1)) := by
  exact power_mul sq0_contains sq0_contains (by decide +kernel)
def sq2 : CBox := ⟨⟨999999999928189176709775095874,999999999928189176709775095893⟩,⟨11984224905069706421511465,11984224905069706421549632⟩⟩
lemma sq2_contains : sq2.Contains (Complex.exp ((1/2048:ℂ)*(Complex.I*Real.pi/512)) ^ (2^2)) := by
  exact power_mul sq1_contains sq1_contains (by decide +kernel)
def sq3 : CBox := ⟨⟨999999999712756706849413972198,999999999712756706849413972238⟩,⟨23968449808418218729166383,23968449808418218729242718⟩⟩
lemma sq3_contains : sq3.Contains (Complex.exp ((1/2048:ℂ)*(Complex.I*Real.pi/512)) ^ (2^3)) := by
  exact power_mul sq2_contains sq2_contains (by decide +kernel)
def sq4 : CBox := ⟨⟨999999998851026827562673307750,999999998851026827562673307835⟩,⟨47936899603066884548963602,47936899603066884549116273⟩⟩
lemma sq4_contains : sq4.Contains (Complex.exp ((1/2048:ℂ)*(Complex.I*Real.pi/512)) ^ (2^4)) := by
  exact power_mul sq3_contains sq3_contains (by decide +kernel)
def sq5 : CBox := ⟨⟨999999995404107312890971933039,999999995404107312890971933225⟩,⟨95873799095977345870436433,95873799095977345870741776⟩⟩
lemma sq5_contains : sq5.Contains (Complex.exp ((1/2048:ℂ)*(Complex.I*Real.pi/512)) ^ (2^5)) := by
  exact power_mul sq4_contains sq4_contains (by decide +kernel)
def sq6 : CBox := ⟨⟨999999981616429293808346915158,999999981616429293808346915590⟩,⟨191747597310703307439748006,191747597310703307440358693⟩⟩
lemma sq6_contains : sq6.Contains (Complex.exp ((1/2048:ℂ)*(Complex.I*Real.pi/512)) ^ (2^6)) := by
  exact power_mul sq5_contains sq5_contains (by decide +kernel)
def sq7 : CBox := ⟨⟨999999926465717851144731480045,999999926465717851144731481144⟩,⟨383495187571395589072138569,383495187571395589073359944⟩⟩
lemma sq7_contains : sq7.Contains (Complex.exp ((1/2048:ℂ)*(Complex.I*Real.pi/512)) ^ (2^7)) := by
  exact power_mul sq6_contains sq6_contains (by decide +kernel)
def sq8 : CBox := ⟨⟨999999705862882219160228215725,999999705862882219160228218860⟩,⟨766990318742704526937922133,766990318742704526940364884⟩⟩
lemma sq8_contains : sq8.Contains (Complex.exp ((1/2048:ℂ)*(Complex.I*Real.pi/512)) ^ (2^8)) := by
  exact power_mul sq7_contains sq7_contains (by decide +kernel)
def sq9 : CBox := ⟨⟨999998823451701909929025703388,999998823451701909929025713406⟩,⟨1533980186284765612302404697,1533980186284765612307290204⟩⟩
lemma sq9_contains : sq9.Contains (Complex.exp ((1/2048:ℂ)*(Complex.I*Real.pi/512)) ^ (2^9)) := by
  exact power_mul sq8_contains sq8_contains (by decide +kernel)
def sq10 : CBox := ⟨⟨999995293809576171511580101109,999995293809576171511580136135⟩,⟨3067956762965976270142780566,3067956762965976270152551600⟩⟩
lemma sq10_contains : sq10.Contains (Complex.exp ((1/2048:ℂ)*(Complex.I*Real.pi/512)) ^ (2^10)) := by
  exact power_mul sq9_contains sq9_contains (by decide +kernel)
def sq11 : CBox := ⟨⟨999981175282601142656990344453,999981175282601142656990474460⟩,⟨6135884649154475359635064613,6135884649154475359654606805⟩⟩
lemma sq11_contains : sq11.Contains (Complex.exp ((1/2048:ℂ)*(Complex.I*Real.pi/512)) ^ (2^11)) := by
  exact power_mul sq10_contains sq10_contains (by decide +kernel)
lemma phase_contains : sq11.Contains (rootPhase 1) := by
  have hh := sq11_contains
  rw [← Complex.exp_nat_mul] at hh
  convert hh using 1
  unfold rootPhase
  congr 1
  norm_num
  ring
def root0 : CBox := ⟨⟨1000000000000000000000000000000,1000000000000000000000000000000⟩,⟨0,0⟩⟩
lemma root0_contains : root0.Contains (rootPhase 0) := by
  simpa [rootPhase] using CBox.rat_contains (a:=root0) (mr:=1) (nr:=1) (mi:=0) (ni:=1) (by decide +kernel)
def root1 : CBox := sq11
lemma root1_contains : root1.Contains (rootPhase 1) := phase_contains
def root2 : CBox := ⟨⟨999924701839144540921646128276,999924701839144540921646628103⟩,⟨12271538285719926079397921046,12271538285719926079437006290⟩⟩
lemma root2_contains : root2.Contains (rootPhase 2) := by
  have hh := CBox.mul_contains root1_contains root1_contains (c:=root2) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def mid3 : CBox := root2
lemma mid3_contains : mid3.Contains (rootPhase 2) := root2_contains
def root3 : CBox := ⟨⟨999830581795823422015721465999,999830581795823422015722575450⟩,⟨18406729905804820927350799344,18406729905804820927409429236⟩⟩
lemma root3_contains : root3.Contains (rootPhase 3) := by
  have hh := CBox.mul_contains mid3_contains root1_contains (c:=root3) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def root4 : CBox := ⟨⟨999698818696204220115764218405,999698818696204220115766177257⟩,⟨24541228522912288031713840299,24541228522912288031792017169⟩⟩
lemma root4_contains : root4.Contains (rootPhase 4) := by
  have hh := CBox.mul_contains root2_contains root2_contains (c:=root4) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def mid5 : CBox := root4
lemma mid5_contains : mid5.Contains (rootPhase 4) := root4_contains
def root5 : CBox := ⟨⟨999529417501093163079701092225,999529417501093163079704140282⟩,⟨30674803176636625933995159302,30674803176636625934092886218⟩⟩
lemma root5_contains : root5.Contains (rootPhase 5) := by
  have hh := CBox.mul_contains mid5_contains root1_contains (c:=root5) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def root6 : CBox := ⟨⟨999322384588349500896217806309,999322384588349500896222183205⟩,⟨36807222941358832324301639063,36807222941358832324418919825⟩⟩
lemma root6_contains : root6.Contains (rootPhase 6) := by
  have hh := CBox.mul_contains root3_contains root3_contains (c:=root6) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def mid7 : CBox := root6
lemma mid7_contains : mid7.Contains (rootPhase 6) := root6_contains
def root7 : CBox := ⟨⟨999077727752645382888777640789,999077727752645382888783586437⟩,⟨42938256934940823077088299429,42938256934940823077225138576⟩⟩
lemma root7_contains : root7.Contains (rootPhase 7) := by
  have hh := CBox.mul_contains mid7_contains root1_contains (c:=root7) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def root8 : CBox := ⟨⟨998795456205172392714765921460,998795456205172392714773675098⟩,⟨49067674327418014254913540834,49067674327418014255069943630⟩⟩
lemma root8_contains : root8.Contains (rootPhase 8) := by
  have hh := CBox.mul_contains root4_contains root4_contains (c:=root8) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def mid9 : CBox := root8
lemma mid9_contains : mid9.Contains (rootPhase 8) := root8_contains
def root9 : CBox := ⟨⟨998475580573294752208551851437,998475580573294752208561653340⟩,⟨55195244349689939809400887170,55195244349689939809576859630⟩⟩
lemma root9_contains : root9.Contains (rootPhase 9) := by
  have hh := CBox.mul_contains mid9_contains root1_contains (c:=root9) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def root10 : CBox := ⟨⟨998118112900149207125146994418,998118112900149207125159083172⟩,⟨61320736302208577782562743931,61320736302208577782758292784⟩⟩
lemma root10_contains : root10.Contains (rootPhase 10) := by
  have hh := CBox.mul_contains root5_contains root5_contains (c:=root10) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def mid11 : CBox := root10
lemma mid11_contains : mid11.Contains (rootPhase 10) := root10_contains
def root11 : CBox := ⟨⟨997723066644191609848536006189,997723066644191609848550622686⟩,⟨67443919563664057897915353494,67443919563664057898130486230⟩⟩
lemma root11_contains : root11.Contains (rootPhase 11) := by
  have hh := CBox.mul_contains mid11_contains root1_contains (c:=root11) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def root12 : CBox := ⟨⟨997290456678690216135584387171,997290456678690216135601768591⟩,⟨73564563599667423529403324005,73564563599667423529638048791⟩⟩
lemma root12_contains : root12.Contains (rootPhase 12) := by
  have hh := CBox.mul_contains root6_contains root6_contains (c:=root12) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def mid13 : CBox := root12
lemma mid13_contains : mid13.Contains (rootPhase 12) := root12_contains
def root13 : CBox := ⟨⟨996820299291165714972614437270,996820299291165714972634825876⟩,⟨79682437971430121147053118516,79682437971430121147307444340⟩⟩
lemma root13_contains : root13.Contains (rootPhase 13) := by
  have hh := CBox.mul_contains mid13_contains root1_contains (c:=root13) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def root14 : CBox := ⟨⟨996312612182778012627208846523,996312612182778012627232478122⟩,⟨85797312344439890461483543204,85797312344439890461757479685⟩⟩
lemma root14_contains : root14.Contains (rootPhase 14) := by
  have hh := CBox.mul_contains root7_contains root7_contains (c:=root14) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def mid15 : CBox := root14
lemma mid15_contains : mid15.Contains (rootPhase 14) := root14_contains
def root15 : CBox := ⟨⟨995767414467659793982475739448,995767414467659793982502857641⟩,⟨91908956497132728624912926173,91908956497132728625206483785⟩⟩
lemma root15_contains : root15.Contains (rootPhase 15) := by
  have hh := CBox.mul_contains mid15_contains root1_contains (c:=root15) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def root16 : CBox := ⟨⟨995184726672196886244814317906,995184726672196886244845155147⟩,⟨98017140329560601994112233761,98017140329560601994425423472⟩⟩
lemma root16_contains : root16.Contains (rootPhase 16) := by
  have hh := CBox.mul_contains root8_contains root8_contains (c:=root16) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def mid17 : CBox := root16
lemma mid17_contains : mid17.Contains (rootPhase 16) := root16_contains
def root17 : CBox := ⟨⟨994564570734255452119080696669,994564570734255452119115499878⟩,⟨104121633872054579120855258389,104121633872054579121188092253⟩⟩
lemma root17_contains : root17.Contains (rootPhase 17) := by
  have hh := CBox.mul_contains mid17_contains root1_contains (c:=root17) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def root18 : CBox := ⟨⟨993906970002356041546894183945,993906970002356041546933183553⟩,⟨110222207293883058807805211978,110222207293883058808157702424⟩⟩
lemma root18_contains : root18.Contains (rootPhase 18) := by
  have hh := CBox.mul_contains root9_contains root9_contains (c:=root18) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def mid19 : CBox := root18
lemma mid19_contains : mid19.Contains (rootPhase 18) := root18_contains
def root19 : CBox := ⟨⟨993211949234794533104569119976,993211949234794533104612564890⟩,⟨116318630911904767252445068577,116318630911904767252817229136⟩⟩
lemma root19_contains : root19.Contains (rootPhase 19) := by
  have hh := CBox.mul_contains mid19_contains root1_contains (c:=root19) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def root20 : CBox := ⟨⟨992479534598709998156731928937,992479534598709998156780043346⟩,⟨122410675199216198498599883954,122410675199216198498991728242⟩⟩
lemma root20_contains : root20.Contains (rootPhase 20) := by
  have hh := CBox.mul_contains root10_contains root10_contains (c:=root20) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def mid21 : CBox := root20
lemma mid21_contains : mid21.Contains (rootPhase 20) := root20_contains
def root21 : CBox := ⟨⟨991709753669099522860010994595,991709753669099522860064033613⟩,⟨128498110793793172624305641693,128498110793793172624717184970⟩⟩
lemma root21_contains : root21.Contains (rootPhase 21) := by
  have hh := CBox.mul_contains mid21_contains root1_contains (c:=root21) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def root22 : CBox := ⟨⟨990902635427780025108194293916,990902635427780025108252479139⟩,⟨134580708507126186316243086075,134580708507126186316674343449⟩⟩
lemma root22_contains : root22.Contains (rootPhase 22) := by
  have hh := CBox.mul_contains root11_contains root11_contains (c:=root22) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def mid23 : CBox := root22
lemma mid23_contains : mid23.Contains (rootPhase 22) := root22_contains
def root23 : CBox := ⟨⟨990058210262297105505859783471,990058210262297105505923372572⟩,⟨140658239332849230714668127797,140658239332849230715119115978⟩⟩
lemma root23_contains : root23.Contains (rootPhase 23) := by
  have hh := CBox.mul_contains mid23_contains root1_contains (c:=root23) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def root24 : CBox := ⟨⟨989176509964780973451622932037,989176509964780973451692135539⟩,⟨146730474455361751658723995762,146730474455361751659194730654⟩⟩
lemma root24_contains : root24.Contains (rootPhase 24) := by
  have hh := CBox.mul_contains root12_contains root12_contains (c:=root24) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def mid25 : CBox := root24
lemma mid25_contains : mid25.Contains (rootPhase 24) := root24_contains
def root25 : CBox := ⟨⟨988257567730749491404737417788,988257567730749491404812504398⟩,⟨152797185258443427720205041587,152797185258443427720695541996⟩⟩
lemma root25_contains : root25.Contains (rootPhase 25) := by
  have hh := CBox.mul_contains mid25_contains root1_contains (c:=root25) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def root26 : CBox := ⟨⟨987301418157858382399756207339,987301418157858382399837385496⟩,⟨158858143333861441684248329921,158858143333861441684758613438⟩⟩
lemma root26_contains : root26.Contains (rootPhase 26) := by
  have hh := CBox.mul_contains root13_contains root13_contains (c:=root26) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def mid27 : CBox := root26
lemma mid27_contains : mid27.Contains (rootPhase 26) := root26_contains
def root27 : CBox := ⟨⟨986308097244598647863233265465,986308097244598647863320805928⟩,⟨164913120489969921418046601323,164913120489969921418576688021⟩⟩
lemma root27_contains : root27.Contains (rootPhase 27) := by
  have hh := CBox.mul_contains mid27_contains root1_contains (c:=root27) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def root28 : CBox := ⟨⟨985277642388941244773949358950,985277642388941244774043453899⟩,⟨170961888760301226363494340133,170961888760301226364044247932⟩⟩
lemma root28_contains : root28.Contains (rootPhase 28) := by
  have hh := CBox.mul_contains root14_contains root14_contains (c:=root28) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def mid29 : CBox := root28
lemma mid29_contains : mid29.Contains (rootPhase 28) := root28_contains
def root29 : CBox := ⟨⟨984210092386929073193800299353,984210092386929073193901235765⟩,⟨177004220412148756196686295999,177004220412148756197256047514⟩⟩
lemma root29_contains : root29.Contains (rootPhase 29) := by
  have hh := CBox.mul_contains mid29_contains root1_contains (c:=root29) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def root30 : CBox := ⟨⟨983105487431216327180221903394,983105487431216327180329871369⟩,⟨183039887955140958516373474858,183039887955140958516963089877⟩⟩
lemma root30_contains : root30.Contains (rootPhase 30) := by
  have hh := CBox.mul_contains root15_contains root15_contains (c:=root30) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def mid31 : CBox := root30
lemma mid31_contains : mid31.Contains (rootPhase 30) := root30_contains
def root31 : CBox := ⟨⟨981963869109555264072763540086,981963869109555264072878828651⟩,⟨189068664149806212754833150480,189068664149806212755442652712⟩⟩
lemma root31_contains : root31.Contains (rootPhase 31) := by
  have hh := CBox.mul_contains mid31_contains root1_contains (c:=root31) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def root32 : CBox := ⟨⟨980785280403230449126092123358,980785280403230449126214896781⟩,⟨195090322016128267848114573460,195090322016128267848743981851⟩⟩
lemma root32_contains : root32.Contains (rootPhase 32) := by
  have hh := CBox.mul_contains root16_contains root16_contains (c:=root32) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def mid33 : CBox := root32
lemma mid33_contains : mid33.Contains (rootPhase 32) := root32_contains
def root33 : CBox := ⟨⟨979569765685440534439230286370,979569765685440534439360859461⟩,⟨201104634842091911558267612314,201104634842091911558916954238⟩⟩
lemma root33_contains : root33.Contains (rootPhase 33) := by
  have hh := CBox.mul_contains mid33_contains root1_contains (c:=root33) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def root34 : CBox := ⟨⟨978317370719627633106138425625,978317370719627633106276964114⟩,⟨207111376192218549707934419905,207111376192218549708603716978⟩⟩
lemma root34_contains : root34.Contains (rootPhase 34) := by
  have hh := CBox.mul_contains root17_contains root17_contains (c:=root34) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def mid35 : CBox := root34
lemma mid35_contains : mid35.Contains (rootPhase 34) := root34_contains
def root35 : CBox := ⟨⟨977028142657754351485758481373,977028142657754351485905298583⟩,⟨213110319916091373967570220348,213110319916091373968259500270⟩⟩
lemma root35_contains : root35.Contains (rootPhase 35) := by
  have hh := CBox.mul_contains mid35_contains root1_contains (c:=root35) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def root36 : CBox := ⟨⟨975702130038528544460281858097,975702130038528544460437086613⟩,⟨219101240156869797227544524467,219101240156869797228253807136⟩⟩
lemma root36_contains : root36.Contains (rootPhase 36) := by
  have hh := CBox.mul_contains root18_contains root18_contains (c:=root36) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def mid37 : CBox := root36
lemma mid37_contains : mid37.Contains (rootPhase 36) := root36_contains
def root37 : CBox := ⟨⟨974339382785575860518601354327,974339382785575860518765340565⟩,⟨225083911359792835991443336743,225083911359792835992172654368⟩⟩
lemma root37_contains : root37.Contains (rootPhase 37) := by
  have hh := CBox.mul_contains mid37_contains root1_contains (c:=root37) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def root38 : CBox := ⟨⟨972939952205560145467593273683,972939952205560145467766152113⟩,⟨231058108280671119643031444831,231058108280671119643780820366⟩⟩
lemma root38_contains : root38.Contains (rootPhase 38) := by
  have hh := CBox.mul_contains root19_contains root19_contains (c:=root38) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def mid39 : CBox := root38
lemma mid39_contains : mid39.Contains (rootPhase 38) := root38_contains
def root39 : CBox := ⟨⟨971503890986251775536966029592,971503890986251775537148144721⟩,⟨237023605994367206867525514824,237023605994367206868294980433⟩⟩
lemma root39_contains : root39.Contains (rootPhase 39) := by
  have hh := CBox.mul_contains mid39_contains root1_contains (c:=root39) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def root40 : CBox := ⟨⟨970031253194543992603843767190,970031253194543992604035204171⟩,⟨242980179903263889948057907060,242980179903263889948847481369⟩⟩
lemma root40_contains : root40.Contains (rootPhase 40) := by
  have hh := CBox.mul_contains root20_contains root20_contains (c:=root40) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def mid41 : CBox := root40
lemma mid41_contains : mid41.Contains (rootPhase 40) := root40_contains
def root41 : CBox := ⟨⟨968522094274417316220940791066,968522094274417316221141943657⟩,⟨248927605745720168110460665898,248927605745720168111270388106⟩⟩
lemma root41_contains : root41.Contains (rootPhase 41) := by
  have hh := CBox.mul_contains mid41_contains root1_contains (c:=root41) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def root42 : CBox := ⟨⟨966976471044852109087065489533,966976471044852109087276453224⟩,⟨254865659604514571553752700314,254865659604514571554582594105⟩⟩
lemma root42_contains : root42.Contains (rootPhase 42) := by
  have hh := CBox.mul_contains root21_contains root21_contains (c:=root42) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def mid43 : CBox := root42
lemma mid43_contains : mid43.Contains (rootPhase 42) := root42_contains
def root43 : CBox := ⟨⟨965394441697689374550681678177,965394441697689374550902836378⟩,⟨260794117915275518279952462403,260794117915275518280802564996⟩⟩
lemma root43_contains : root43.Contains (rootPhase 43) := by
  have hh := CBox.mul_contains mid43_contains root1_contains (c:=root43) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def root44 : CBox := ⟨⟨963776065795439866686294662206,963776065795439866686526051835⟩,⟨266712757474898386325046469368,266712757474898386325916798723⟩⟩
lemma root44_contains : root44.Contains (rootPhase 44) := by
  have hh := CBox.mul_contains root22_contains root22_contains (c:=root44) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def mid45 : CBox := root44
lemma mid45_contains : mid45.Contains (rootPhase 44) := root44_contains
def root45 : CBox := ⟨⟨962121404269041595429426835625,962121404269041595429668898589⟩,⟨272621355449948984493101387265,272621355449948984493991988989⟩⟩
lemma root45_contains : root45.Contains (rootPhase 45) := by
  have hh := CBox.mul_contains mid45_contains root1_contains (c:=root45) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def root46 : CBox := ⟨⟨960430519415565811198849793580,960430519415565811199102577811⟩,⟨278519689385053105207596356922,278519689385053105208507254687⟩⟩
lemma root46_contains : root46.Contains (rootPhase 46) := by
  have hh := CBox.mul_contains root23_contains root23_contains (c:=root46) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def mid47 : CBox := root46
lemma mid47_contains : mid47.Contains (rootPhase 46) := root46_contains
def root47 : CBox := ⟨⟨958703474895871555374452316767,958703474895871555374716253152⟩,⟨284407537211271843618052322018,284407537211271843618983558819⟩⟩
lemma root47_contains : root47.Contains (rootPhase 47) := by
  have hh := CBox.mul_contains mid47_contains root1_contains (c:=root47) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def root48 : CBox := ⟨⟨956940335732208864935596247879,956940335732208864935871299145⟩,⟨290284677254462367635927928894,290284677254462367636879517216⟩⟩
lemma root48_contains : root48.Contains (rootPhase 48) := by
  have hh := CBox.mul_contains root24_contains root24_contains (c:=root48) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def mid49 : CBox := root48
lemma mid49_contains : mid49.Contains (rootPhase 48) := root48_contains
def root49 : CBox := ⟨⟨955141168305770721497947599516,955141168305770721498234281650⟩,⟨296150888243623824121515474166,296150888243623824122487470710⟩⟩
lemma root49_contains : root49.Contains (rootPhase 49) := by
  have hh := CBox.mul_contains mid49_contains root1_contains (c:=root49) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def root50 : CBox := ⟨⟨953306040354193836916521749292,953306040354193836916820053278⟩,⟨302005949319228067003186335211,302005949319228067004178762739⟩⟩
lemma root50_contains : root50.Contains (rootPhase 50) := by
  have hh := CBox.mul_contains root25_contains root25_contains (c:=root50) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def mid51 : CBox := root50
lemma mid51_contains : mid51.Contains (rootPhase 50) := root50_contains
def root51 : CBox := ⟨⟨951435020969008369548948119793,951435020969008369549258533380⟩,⟨307849640041534893681780455999,307849640041534893682793364157⟩⟩
lemma root51_contains : root51.Contains (rootPhase 51) := by
  have hh := CBox.mul_contains mid51_contains root1_contains (c:=root51) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def root52 : CBox := ⟨⟨949528180593036667195699809902,949528180593036667196022229906⟩,⟨313681740398891476656189332551,313681740398891476657222731454⟩⟩
lemma root52_contains : root52.Contains (rootPhase 52) := by
  have hh := CBox.mul_contains root26_contains root26_contains (c:=root52) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def mid53 : CBox := root52
lemma mid53_contains : mid53.Contains (rootPhase 52) := root52_contains
def root53 : CBox := ⟨⟨947585591017741134653141900127,947585591017741134653476908353⟩,⟨319502030816015677901222375558,319502030816015677902276329983⟩⟩
lemma root53_contains : root53.Contains (rootPhase 53) := by
  have hh := CBox.mul_contains mid53_contains root1_contains (c:=root53) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def root54 : CBox := ⟨⟨945607325380521325730690796135,945607325380521325731038316374⟩,⟨325310292162262934135652392352,325310292162262934136726923100⟩⟩
lemma root54_contains : root54.Contains (rootPhase 54) := by
  have hh := CBox.mul_contains root27_contains root27_contains (c:=root54) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def mid55 : CBox := root54
lemma mid55_contains : mid55.Contains (rootPhase 54) := root54_contains
def root55 : CBox := ⟨⟨943593458161960361495037357928,943593458161960361495397945034⟩,⟨331106305759876401736881946046,331106305759876401737977110444⟩⟩
lemma root55_contains : root55.Contains (rootPhase 55) := by
  have hh := CBox.mul_contains mid55_contains root1_contains (c:=root55) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def root56 : CBox := ⟨⟨941544065183020778412235872018,941544065183020778412609317870⟩,⟨336889853392220050688937918668,336889853392220050690053715688⟩⟩
lemma root56_contains : root56.Contains (rootPhase 56) := by
  have hh := CBox.mul_contains root28_contains root28_contains (c:=root56) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def mid57 : CBox := root56
lemma mid57_contains : mid57.Contains (rootPhase 56) := root56_contains
def root57 : CBox := ⟨⟨939459223602189911962385878967,939459223602189911962772870165⟩,⟨342660717311994397592460117008,342660717311994397593596628078⟩⟩
lemma root57_contains : root57.Contains (rootPhase 57) := by
  have hh := CBox.mul_contains mid57_contains root1_contains (c:=root57) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def root58 : CBox := ⟨⟨937339011912574923201606417698,937339011912574923202006799815⟩,⟨348418680249434568418980113112,348418680249434568420137355837⟩⟩
lemma root58_contains : root58.Contains (rootPhase 58) := by
  have hh := CBox.mul_contains root29_contains root29_contains (c:=root58) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def mid59 : CBox := root58
lemma mid59_contains : mid59.Contains (rootPhase 58) := root58_contains
def root59 : CBox := ⟨⟨935183509938947577641904129382,935183509938947577642318535396⟩,⟨354163525420490382357060650327,354163525420490382358238690922⟩⟩
lemma root59_contains : root59.Contains (rootPhase 59) := by
  have hh := CBox.mul_contains mid59_contains root1_contains (c:=root59) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def root60 : CBox := ⟨⟨932992798834738887711346829290,932992798834738887711774963242⟩,⟨359895036534988148774762728754,359895036534988148775961561168⟩⟩
lemma root60_contains : root60.Contains (rootPhase 60) := by
  have hh := CBox.mul_contains root30_contains root30_contains (c:=root60) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def mid61 : CBox := root60
lemma mid61_contains : mid61.Contains (rootPhase 60) := root60_contains
def root61 : CBox := ⟨⟨930766961078983731944548401569,930766961078983731944991037794⟩,⟨365612997804773870011397291200,365612997804773870012617007542⟩⟩
lemma root61_contains : root61.Contains (rootPhase 61) := by
  have hh := CBox.mul_contains mid61_contains root1_contains (c:=root61) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def root62 : CBox := ⟨⟨928506080473215565936833019042,928506080473215565937289912999⟩,⟨371317193951837543411579538809,371317193951837543412820152060⟩⟩
lemma root62_contains : root62.Contains (rootPhase 62) := by
  have hh := CBox.mul_contains root31_contains root31_contains (c:=root62) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def mid63 : CBox := root62
lemma mid63_contains : mid63.Contains (rootPhase 62) := root62_contains
def root63 : CBox := ⟨⟨926210242138311341974448163407,926210242138311341974920038088⟩,⟨377007410216418256726205514990,377007410216418256727467101655⟩⟩
lemma root63_contains : root63.Contains (rootPhase 63) := by
  have hh := CBox.mul_contains mid63_contains root1_contains (c:=root63) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def root64 : CBox := ⟨⟨923879532511286756127827289675,923879532511286756128313701380⟩,⟨382683432365089771728090778077,382683432365089771729373310862⟩⟩
lemma root64_contains : root64.Contains (rootPhase 64) := by
  have hh := CBox.mul_contains root32_contains root32_contains (c:=root64) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def mid65 : CBox := root64
lemma mid65_contains : mid65.Contains (rootPhase 64) := root64_contains
def root65 : CBox := ⟨⟨921514039342041943465029248274,921514039342041943465531118880⟩,⟨388345046698826291624617345776,388345046698826291625920943367⟩⟩
lemma root65_contains : root65.Contains (rootPhase 65) := by
  have hh := CBox.mul_contains mid65_contains root1_contains (c:=root65) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def root66 : CBox := ⟨⟨919113851690057743908099648503,919113851690057743908616630749⟩,⟨393992040061048108595805441378,393992040061048108597130110519⟩⟩
lemma root66_contains : root66.Contains (rootPhase 66) := by
  have hh := CBox.mul_contains root33_contains root33_contains (c:=root66) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def mid67 : CBox := root66
lemma mid67_contains : mid67.Contains (rootPhase 66) := root66_contains
def root67 : CBox := ⟨⟨916679059921042663116067354785,916679059921042663116600274276⟩,⟨399624199845646828543726709667,399624199845646828545072538737⟩⟩
lemma root67_contains : root67.Contains (rootPhase 67) := by
  have hh := CBox.mul_contains mid67_contains root1_contains (c:=root67) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def root68 : CBox := ⟨⟨914209755703530654634613880580,914209755703530654635162187877⟩,⟨405241314004989870908083866314,405241314004989870909450822014⟩⟩
lemma root68_contains : root68.Contains (rootPhase 68) := by
  have hh := CBox.mul_contains root34_contains root34_contains (c:=root68) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def mid69 : CBox := root68
lemma mid69_contains : mid69.Contains (rootPhase 68) := root68_contains
def root69 : CBox := ⟨⟨911706032005429851403984525479,911706032005429851404549248095⟩,⟨410843171057903942183062018801,410843171057903942184450231466⟩⟩
lemma root69_contains : root69.Contains (rootPhase 69) := by
  have hh := CBox.mul_contains mid69_contains root1_contains (c:=root69) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def root70 : CBox := ⟨⟨909167983090522376563460322517,909167983090522376564040996940⟩,⟨416429560097637182562187004298,416429560097637182563596472588⟩⟩
lemma root70_contains : root70.Contains (rootPhase 70) := by
  have hh := CBox.mul_contains root35_contains root35_contains (c:=root70) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def mid71 : CBox := root70
lemma mid71_contains : mid71.Contains (rootPhase 70) := root70_contains
def root71 : CBox := ⟨⟨906595704514915365332523940481,906595704514915365333121508453⟩,⟨422000270799799685940868698904,422000270799799685942299524888⟩⟩
lemma root71_contains : root71.Contains (rootPhase 71) := by
  have hh := CBox.mul_contains mid71_contains root1_contains (c:=root71) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def root72 : CBox := ⟨⟨903989293123443331585751789790,903989293123443331586365512803⟩,⟨427555093430282094320540276015,427555093430282094321992394759⟩⟩
lemma root72_contains : root72.Contains (rootPhase 72) := by
  have hh := CBox.mul_contains root36_contains root36_contains (c:=root72) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def mid73 : CBox := root72
lemma mid73_contains : mid73.Contains (rootPhase 72) := root72_contains
def root73 : CBox := ⟨⟨901348847046022014570285072522,901348847046022014570916166904⟩,⟨433093818853151968483788600171,433093818853151968485262178831⟩⟩
lemma root73_contains : root73.Contains (rootPhase 73) := by
  have hh := CBox.mul_contains mid73_contains root1_contains (c:=root73) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def root74 : CBox := ⟨⟨898674465693953843041503461092,898674465693953843042151332920⟩,⟨438616238538527637646584211668,438616238538527637648079238766⟩⟩
lemma root74_contains : root74.Contains (rootPhase 74) := by
  have hh := CBox.mul_contains root37_contains root37_contains (c:=root74) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def mid75 : CBox := root74
lemma mid75_contains : mid75.Contains (rootPhase 74) := root74_contains
def root75 : CBox := ⟨⟨895966249756185155914074156363,895966249756185155914739877666⟩,⟨444122144570429231641620309370,444122144570429231643136902684⟩⟩
lemma root75_contains : root75.Contains (rootPhase 75) := by
  have hh := CBox.mul_contains mid75_contains root1_contains (c:=root75) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def root76 : CBox := ⟨⟨893224301195515320341917869866,893224301195515320342600569117⟩,⟨449611329654606600045837888762,449611329654606600047375973484⟩⟩
lemma root76_contains : root76.Contains (rootPhase 76) := by
  have hh := CBox.mul_contains root38_contains root38_contains (c:=root76) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def mid77 : CBox := root76
lemma mid77_contains : mid77.Contains (rootPhase 76) := root76_contains
def root77 : CBox := ⟨⟨890448723244757889951638811140,890448723244757889952339837567⟩,⟨455083587126343823535404866729,455083587126343823536964625475⟩⟩
lemma root77_contains : root77.Contains (rootPhase 77) := by
  have hh := CBox.mul_contains mid77_contains root1_contains (c:=root77) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def root78 : CBox := ⟨⟨887639620402853947759657022816,887639620402853947760375636956⟩,⟨460538710958240023632709349462,460538710958240023634290758298⟩⟩
lemma root78_contains : root78.Contains (rootPhase 78) := by
  have hh := CBox.mul_contains root39_contains root39_contains (c:=root78) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def mid79 : CBox := root78
lemma mid79_contains : mid79.Contains (rootPhase 78) := root78_contains
def root79 : CBox := ⟨⟨884797098430937780103468947937,884797098430937780104206367228⟩,⟨465976495767966177902276085611,465976495767966177903879280309⟩⟩
lemma root79_contains : root79.Contains (rootPhase 79) := by
  have hh := CBox.mul_contains mid79_contains root1_contains (c:=root79) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def root80 : CBox := ⟨⟨881921264348355029712205790646,881921264348355029712960892171⟩,⟨471396736825997648555899829334,471396736825997648557524683632⟩⟩
lemma root80_contains : root80.Contains (rootPhase 80) := by
  have hh := CBox.mul_contains root40_contains root40_contains (c:=root80) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def mid81 : CBox := root80
lemma mid81_contains : mid81.Contains (rootPhase 80) := root80_contains
def root81 : CBox := ⟨⟨879012226428633477830758814115,879012226428633477831533198127⟩,⟨476799230063322133341662345221,476799230063322133343309098108⟩⟩
lemma root81_contains : root81.Contains (rootPhase 81) := by
  have hh := CBox.mul_contains mid81_contains root1_contains (c:=root81) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def root82 : CBox := ⟨⟨876070094195406607095265955103,876070094195406607096058720982⟩,⟨482183772079122748516840713183,482183772079122748518509325747⟩⟩
lemma root82_contains : root82.Contains (rootPhase 82) := by
  have hh := CBox.mul_contains root41_contains root41_contains (c:=root82) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def mid83 : CBox := root82
lemma mid83_contains : mid83.Contains (rootPhase 82) := root82_contains
def root83 : CBox := ⟨⟨873094978418290098635493511685,873094978418290098636306037879⟩,⟨487550160148435954640973146475,487550160148435954642663774966⟩⟩
lemma root83_contains : root83.Contains (rootPhase 83) := by
  have hh := CBox.mul_contains mid83_contains root1_contains (c:=root83) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def root84 : CBox := ⟨⟨870086991108711418651686387463,870086991108711418652517404172⟩,⟨492898192229784036872506721660,492898192229784036874219232001⟩⟩
lemma root84_contains : root84.Contains (rootPhase 84) := by
  have hh := CBox.mul_contains root42_contains root42_contains (c:=root84) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def mid85 : CBox := root84
lemma mid85_contains : mid85.Contains (rootPhase 84) := root84_contains
def root85 : CBox := ⟨⟨867046245515692651479575141378,867046245515692651480426395639⟩,⟨498227666972781852410455649293,498227666972781852412190293907⟩⟩
lemma root85_contains : root85.Contains (rootPhase 85) := by
  have hh := CBox.mul_contains mid85_contains root1_contains (c:=root85) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def root86 : CBox := ⟨⟨863972856121586737917512592763,863972856121586737918383006071⟩,⟨503538383725717558691330585693,503538383725717558693087307846⟩⟩
lemma root86_contains : root86.Contains (rootPhase 86) := by
  have hh := CBox.mul_contains root43_contains root43_contains (c:=root86) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def mid87 : CBox := root86
lemma mid87_contains : mid87.Contains (rootPhase 86) := root86_contains
def root87 : CBox := ⟨⟨860866938637767279343934622372,860866938637767279344825750907⟩,⟨508830142543107036931204442212,508830142543107036932983421439⟩⟩
lemma root87_contains : root87.Contains (rootPhase 87) := by
  have hh := CBox.mul_contains mid87_contains root1_contains (c:=root87) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def root88 : CBox := ⟨⟨857728610000272069901606682241,857728610000272069902516953699⟩,⟨514102744193221726593140619537,514102744193221726594941653874⟩⟩
lemma root88_contains : root88.Contains (rootPhase 88) := by
  have hh := CBox.mul_contains root44_contains root44_contains (c:=root88) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def mid89 : CBox := root88
lemma mid89_contains : mid89.Contains (rootPhase 88) := root88_contains
def root89 : CBox := ⟨⟨854557988365400520767183860909,854557988365400520768115324377⟩,⟨519355990165589587361268170738,519355990165589587363091585227⟩⟩
lemma root89_contains : root89.Contains (rootPhase 89) := by
  have hh := CBox.mul_contains mid89_contains root1_contains (c:=root89) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def root90 : CBox := ⟨⟨851355193105265142260597380642,851355193105265142261548762660⟩,⟨524589682678468906214528156962,524589682678468906216373873992⟩⟩
lemma root90_contains : root90.Contains (rootPhase 90) := by
  have hh := CBox.mul_contains root45_contains root45_contains (c:=root90) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def mid91 : CBox := root90
lemma mid91_contains : mid91.Contains (rootPhase 90) := root90_contains
def root91 : CBox := ⟨⟨848120344803297251278425200214,848120344803297251279398251744⟩,⟨529803624686294668215475672835,529803624686294668217343898239⟩⟩
lemma root91_contains : root91.Contains (rootPhase 91) := by
  have hh := CBox.mul_contains mid91_contains root1_contains (c:=root91) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def root92 : CBox := ⟨⟨844853565249707073258848247049,844853565249707073259841216356⟩,⟨534997619887097210662489279013,534997619887097210664379797813⟩⟩
lemma root92_contains : root92.Contains (rootPhase 92) := by
  have hh := CBox.mul_contains root46_contains root46_contains (c:=root92) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def mid93 : CBox := root92
lemma mid93_contains : mid93.Contains (rootPhase 92) := root92_contains
def root93 : CBox := ⟨⟨841554977436898409602760813088,841554977436898409603775928572⟩,⟨540171472729892881297249011411,540171472729892881299162167213⟩⟩
lemma root93_contains : root93.Contains (rootPhase 93) := by
  have hh := CBox.mul_contains mid93_contains root1_contains (c:=root93) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def root94 : CBox := ⟨⟨838224705554838043186243104872,838224705554838043187278879862⟩,⟨545324988422046422313382043034,545324988422046422315317733943⟩⟩
lemma root94_contains : root94.Contains (rootPhase 94) := by
  have hh := CBox.mul_contains root47_contains root47_contains (c:=root94) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def mid95 : CBox := root94
lemma mid95_contains : mid95.Contains (rootPhase 94) := root94_contains
def root95 : CBox := ⟨⟨834862874986380056303631567472,834862874986380056304689965961⟩,⟨550457972936604802976675590386,550457972936604802978634051897⟩⟩
lemma root95_contains : root95.Contains (rootPhase 95) := by
  have hh := CBox.mul_contains mid95_contains root1_contains (c:=root95) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def root96 : CBox := ⟨⟨831469612302545237078003531201,831469612302545237079082409521⟩,⟨555570233019602224742207628610,555570233019602224744188541443⟩⟩
lemma root96_contains : root96.Contains (rootPhase 96) := by
  have hh := CBox.mul_contains root48_contains root48_contains (c:=root96) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def mid97 : CBox := root96
lemma mid97_contains : mid97.Contains (rootPhase 96) := root96_contains
def root97 : CBox := ⟨⟨828045045257755752066726367091,828045045257755752067828344913⟩,⟨560661576197336023839077883310,560661576197336023841081699694⟩⟩
lemma root97_contains : root97.Contains (rootPhase 97) := by
  have hh := CBox.mul_contains mid97_contains root1_contains (c:=root97) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def root98 : CBox := ⟨⟨824589302785025264473986955615,824589302785025264475110314712⟩,⟨565731810783613197389123536349,565731810783613197391150126517⟩⟩
lemma root98_contains : root98.Contains (rootPhase 98) := by
  have hh := CBox.mul_contains root49_contains root49_contains (c:=root98) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def mid99 : CBox := root98
lemma mid99_contains : mid99.Contains (rootPhase 98) := root98_contains
def root99 : CBox := ⟨⟨821102514991104679059597347595,821102514991104679060744283312⟩,⟨570780745886967280232002073386,570780745886967280234051706038⟩⟩
lemma root99_contains : root99.Contains (rootPhase 99) := by
  have hh := CBox.mul_contains mid99_contains root1_contains (c:=root99) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def root100 : CBox := ⟨⟨817584813151583696504071845716,817584813151583696505240033735⟩,⟨575808191417845300745312462358,575808191417845300747384815831⟩⟩
lemma root100_contains : root100.Contains (rootPhase 100) := by
  have hh := CBox.mul_contains root50_contains root50_contains (c:=root100) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def mid101 : CBox := root100
lemma mid101_contains : mid101.Contains (rootPhase 100) := root100_contains
def root101 : CBox := ⟨⟨814036329705948361653650649265,814036329705948361654842889862⟩,⟨580813958095764545074925802439,580813958095764545077021337027⟩⟩
lemma root101_contains : root101.Contains (rootPhase 101) := by
  have hh := CBox.mul_contains mid101_contains root1_contains (c:=root101) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def root102 : CBox := ⟨⟨810457198252594791725821340830,810457198252594791727035664370⟩,⟨585797857456438860327401924903,585797857456438860329520478916⟩⟩
lemma root102_contains : root102.Contains (rootPhase 102) := by
  have hh := CBox.mul_contains root51_contains root51_contains (c:=root102) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def mid103 : CBox := root102
lemma mid103_contains : mid103.Contains (rootPhase 102) := root102_contains
def root103 : CBox := ⟨⟨806847553543799272205614907420,806847553543799272206853760444⟩,⟨590759701858874228423199350715,590759701858874228425341230065⟩⟩
lemma root103_contains : root103.Contains (rootPhase 103) := by
  have hh := CBox.mul_contains mid103_contains root1_contains (c:=root103) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def root104 : CBox := ⟨⟨803207531480644909805761147193,803207531480644909807021757687⟩,⟨595699304492433343466338502898,595699304492433343468503260195⟩⟩
lemma root104_contains : root104.Contains (rootPhase 104) := by
  have hh := CBox.mul_contains root52_contains root52_contains (c:=root104) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def mid105 : CBox := root104
lemma mid105_contains : mid105.Contains (rootPhase 104) := root104_contains
def root105 : CBox := ⟨⟨799537269107905033499313247580,799537269107905033500598862738⟩,⟨600616479383868926653168058045,600616479383868926655356283434⟩⟩
lemma root105_contains : root105.Contains (rootPhase 105) := by
  have hh := CBox.mul_contains mid105_contains root1_contains (c:=root105) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def root106 : CBox := ⟨⟨795836904608883536261842398052,795836904608883536263150777147⟩,⟨605511041404325513919909342709,605511041404325513922120838381⟩⟩
lemma root106_contains : root106.Contains (rootPhase 106) := by
  have hh := CBox.mul_contains root53_contains root53_contains (c:=root106) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def mid107 : CBox := root106
lemma mid107_contains : mid107.Contains (rootPhase 106) := root106_contains
def root107 : CBox := ⟨⟨792106577300212351781375435918,792106577300212351782709296344⟩,⟨610382806276309452715624569560,610382806276309452717859682784⟩⟩
lemma root107_contains : root107.Contains (rootPhase 107) := by
  have hh := CBox.mul_contains mid107_contains root1_contains (c:=root107) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def root108 : CBox := ⟨⟨788346427626606262008180801256,788346427626606262009537148447⟩,⟨615231590580626845484176177856,615231590580626845486434449972⟩⟩
lemma root108_contains : root108.Contains (rootPhase 108) := by
  have hh := CBox.mul_contains root54_contains root54_contains (c:=root108) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def mid109 : CBox := root108
lemma mid109_contains : mid109.Contains (rootPhase 108) := root108_contains
def root109 : CBox := ⟨⟨784556597155575233022890441299,784556597155575233024272744920⟩,⟨620057211763289178645520649393,620057211763289178647802687390⟩⟩
lemma root109_contains : root109.Contains (rootPhase 109) := by
  have hh := CBox.mul_contains mid109_contains root1_contains (c:=root109) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def root110 : CBox := ⟨⟨780737228572094478300569355162,780737228572094478301975082108⟩,⟨624859488142386377083315187489,624859488142386377085620752742⟩⟩
lemma root110_contains : root110.Contains (rootPhase 110) := by
  have hh := CBox.mul_contains root55_contains root55_contains (c:=root110) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def mid111 : CBox := root110
lemma mid111_contains : mid111.Contains (rootPhase 110) := root110_contains
def root111 : CBox := ⟨⟨776888465673232450039790322183,776888465673232450041222481975⟩,⟨629638238914927025372213378251,629638238914927025374542864034⟩⟩
lemma root111_contains : root111.Contains (rootPhase 111) := by
  have hh := CBox.mul_contains mid111_contains root1_contains (c:=root111) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def root112 : CBox := ⟨⟨773010453362736960809852164844,773010453362736960811307197685⟩,⟨634393284163645498214393587573,634393284163645498216746351935⟩⟩
lemma root112_contains : root112.Contains (rootPhase 112) := by
  have hh := CBox.mul_contains root56_contains root56_contains (c:=root112) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def mid113 : CBox := root112
lemma mid113_contains : mid113.Contains (rootPhase 112) := root112_contains
def root113 : CBox := ⟨⟨769103337645579639345552791638,769103337645579639347034731312⟩,⟨639124444863775743800699656213,639124444863775743803076492994⟩⟩
lemma root113_contains : root113.Contains (rootPhase 113) := by
  have hh := CBox.mul_contains mid113_contains root1_contains (c:=root113) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def root114 : CBox := ⟨⟨765167265622458925887725281728,765167265622458925889231282027⟩,⟨643831542889791465067287106638,643831542889791465069687731617⟩⟩
lemma root114_contains : root114.Contains (rootPhase 114) := by
  have hh := CBox.mul_contains root57_contains root57_contains (c:=root114) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def mid115 : CBox := root114
lemma mid115_contains : mid115.Contains (rootPhase 114) := root114_contains
def root115 : CBox := ⟨⟨761202385484261814028599986398,761202385484261814030133369662⟩,⟨648514401022112445083750900869,648514401022112445086175758050⟩⟩
lemma root115_contains : root115.Contains (rootPhase 115) := by
  have hh := CBox.mul_contains mid115_contains root1_contains (c:=root115) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def root116 : CBox := ⟨⟨757208846506484547574336927007,757208846506484547575893924530⟩,⟨653172842953776764083382933811,653172842953776764085831392534⟩⟩
lemma root116_contains : root116.Contains (rootPhase 116) := by
  have hh := CBox.mul_contains root58_contains root58_contains (c:=root116) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def mid117 : CBox := root116
lemma mid117_contains : mid117.Contains (rootPhase 116) := root116_contains
def root117 : CBox := ⟨⟨753186799043612482482283930519,753186799043612482483868785065⟩,⟨657806693297078656930351307726,657806693297078656932824156353⟩⟩
lemma root117_contains : root117.Contains (rootPhase 117) := by
  have hh := CBox.mul_contains mid117_contains root1_contains (c:=root117) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def root118 : CBox := ⟨⟨749136394523459325468038835081,749136394523459325469648364444⟩,⟨662415777590171761112228100016,662415777590171761114725003284⟩⟩
lemma root118_contains : root118.Contains (rootPhase 118) := by
  have hh := CBox.mul_contains root59_contains root59_contains (c:=root118) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def mid119 : CBox := root118
lemma mid119_contains : mid119.Contains (rootPhase 118) := root118_contains
def root119 : CBox := ⟨⟨745057785441465962406723164209,745057785441465962408361026433⟩,⟨666999922303637506649301441134,666999922303637506651822899172⟩⟩
lemma root119_contains : root119.Contains (rootPhase 119) := by
  have hh := CBox.mul_contains mid119_contains root1_contains (c:=root119) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def root120 : CBox := ⟨⟨740951125354959091174415196559,740951125354959091176076996020⟩,⟨671558954847018400624513374138,671558954847018400627058544726⟩⟩
lemma root120_contains : root120.Contains (rootPhase 120) := by
  have hh := CBox.mul_contains root60_contains root60_contains (c:=root120) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def mid121 : CBox := root120
lemma mid121_contains : mid121.Contains (rootPhase 120) := root120_contains
def root121 : CBox := ⟨⟨736816568877369875088910802273,736816568877369875090601407389⟩,⟨676092703575315960359544500784,676092703575315960362114387187⟩⟩
lemma root121_contains : root121.Contains (rootPhase 121) := by
  have hh := CBox.mul_contains mid121_contains root1_contains (c:=root121) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def root122 : CBox := ⟨⟨732654271672412834614306656667,732654271672412834616022527312⟩,⟨680600997795453050593544629256,680600997795453050596138839717⟩⟩
lemma root122_contains : root122.Contains (rootPhase 122) := by
  have hh := CBox.mul_contains root61_contains root61_contains (c:=root122) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def mid123 : CBox := root122
lemma mid123_contains : mid123.Contains (rootPhase 122) := root122_contains
def root123 : CBox := ⟨⟨728464390448225196490775136144,728464390448225196492520287951⟩,⟨685083667772700381361155266615,685083667772700381363774362779⟩⟩
lemma root123_contains : root123.Contains (rootPhase 123) := by
  have hh := CBox.mul_contains mid123_contains root1_contains (c:=root123) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def root124 : CBox := ⟨⟨724247082951466920939790932891,724247082951466920941560712589⟩,⟨689540544737066924615822275827,689540544737066924618465414886⟩⟩
lemma root124_contains : root124.Contains (rootPhase 124) := by
  have hh := CBox.mul_contains root62_contains root62_contains (c:=root124) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def mid125 : CBox := root124
lemma mid125_contains : mid125.Contains (rootPhase 124) := root124_contains
def root125 : CBox := ⟨⟨720002507961381629075384090229,720002507961381629077183623899⟩,⟨693971460889654009002814399764,693971460889654009005482591253⟩⟩
lemma root125_contains : root125.Contains (rootPhase 125) := by
  have hh := CBox.mul_contains mid125_contains root1_contains (c:=root125) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def root126 : CBox := ⟨⟨715730825283818654124215052254,715730825283818654126040417623⟩,⟨698376249408972853553882051123,698376249408972853556574840607⟩⟩
lemma root126_contains : root126.Contains (rootPhase 126) := by
  have hh := CBox.mul_contains root63_contains root63_contains (c:=root126) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def mid127 : CBox := root126
lemma mid127_contains : mid127.Contains (rootPhase 126) := root126_contains
def root127 : CBox := ⟨⟨711432195745216441520791832038,711432195745216441522647426545⟩,⟨702754744457225302451971136573,702754744457225302454689153341⟩⟩
lemma root127_contains : root127.Contains (rootPhase 127) := by
  have hh := CBox.mul_contains mid127_contains root1_contains (c:=root127) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def root128 : CBox := ⟨⟨707106781186547524399487715074,707106781186547524401368094808⟩,⟨707106781186547524399889764603,707106781186547524402631859585⟩⟩
lemma root128_contains : root128.Contains (rootPhase 128) := by
  have hh := CBox.mul_contains root64_contains root64_contains (c:=root128) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def mid129 : CBox := root128
lemma mid129_contains : mid129.Contains (rootPhase 128) := root128_contains
def root129 : CBox := ⟨⟨702754744457225302451536602879,702754744457225302453447682740⟩,⟨711432195745216441521163664331,711432195745216441523931155833⟩⟩
lemma root129_contains : root129.Contains (rootPhase 129) := by
  have hh := CBox.mul_contains mid129_contains root1_contains (c:=root129) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def root130 : CBox := ⟨⟨698376249408972853553416653793,698376249408972853555354106747⟩,⟨715730825283818654124554175759,715730825283818654127346540651⟩⟩
lemma root130_contains : root130.Contains (rootPhase 130) := by
  have hh := CBox.mul_contains root65_contains root65_contains (c:=root130) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def mid131 : CBox := root130
lemma mid131_contains : mid131.Contains (rootPhase 130) := root130_contains
def root131 : CBox := ⟨⟨693971460889654009002316084280,693971460889654009004284712135⟩,⟨720002507961381629075692321251,720002507961381629078510262419⟩⟩
lemma root131_contains : root131.Contains (rootPhase 131) := by
  have hh := CBox.mul_contains mid131_contains root1_contains (c:=root131) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def root132 : CBox := ⟨⟨689540544737066924615293673641,689540544737066924617287822923⟩,⟨724247082951466920940066829592,724247082951466920942909246885⟩⟩
lemma root132_contains : root132.Contains (rootPhase 132) := by
  have hh := CBox.mul_contains root66_contains root66_contains (c:=root132) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def mid133 : CBox := root132
lemma mid133_contains : mid133.Contains (rootPhase 132) := root132_contains
def root133 : CBox := ⟨⟨685083667772700381360593852210,685083667772700381362619647719⟩,⟨728464390448225196491020593219,728464390448225196493888762167⟩⟩
lemma root133_contains : root133.Contains (rootPhase 133) := by
  have hh := CBox.mul_contains mid133_contains root1_contains (c:=root133) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def root134 : CBox := ⟨⟨680600997795453050592952392402,680600997795453050595005076409⟩,⟨732654271672412834614519616548,732654271672412834617412938253⟩⟩
lemma root134_contains : root134.Contains (rootPhase 134) := by
  have hh := CBox.mul_contains root67_contains root67_contains (c:=root134) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def mid135 : CBox := root134
lemma mid135_contains : mid135.Contains (rootPhase 134) := root134_contains
def root135 : CBox := ⟨⟨676092703575315960358919138743,676092703575315960361003943352⟩,⟨736816568877369875089092850844,736816568877369875092012108802⟩⟩
lemma root135_contains : root135.Contains (rootPhase 135) := by
  have hh := CBox.mul_contains mid135_contains root1_contains (c:=root135) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def root136 : CBox := ⟨⟨671558954847018400623857971505,671558954847018400625968401114⟩,⟨740951125354959091174565249875,740951125354959091177509011888⟩⟩
lemma root136_contains : root136.Contains (rootPhase 136) := by
  have hh := CBox.mul_contains root68_contains root68_contains (c:=root136) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def mid137 : CBox := root136
lemma mid137_contains : mid137.Contains (rootPhase 136) := root136_contains
def root137 : CBox := ⟨⟨666999922303637506648613049918,666999922303637506650756069500⟩,⟨745057785441465962406842821718,745057785441465962409812697732⟩⟩
lemma root137_contains : root137.Contains (rootPhase 137) := by
  have hh := CBox.mul_contains mid137_contains root1_contains (c:=root137) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def root138 : CBox := ⟨⟨662415777590171761111508938219,662415777590171761113679335637⟩,⟨749136394523459325468126210110,749136394523459325471121518693⟩⟩
lemma root138_contains : root138.Contains (rootPhase 138) := by
  have hh := CBox.mul_contains root69_contains root69_contains (c:=root138) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def mid139 : CBox := root138
lemma mid139_contains : mid139.Contains (rootPhase 138) := root138_contains
def root139 : CBox := ⟨⟨657806693297078656929598815605,657806693297078656931802276921⟩,⟨753186799043612482482340387310,753186799043612482485361999266⟩⟩
lemma root139_contains : root139.Contains (rootPhase 139) := by
  have hh := CBox.mul_contains mid139_contains root1_contains (c:=root139) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def root140 : CBox := ⟨⟨653172842953776764082600364891,653172842953776764084830114600⟩,⟨757208846506484547574361549512,757208846506484547577408056387⟩⟩
lemma root140_contains : root140.Contains (rootPhase 140) := by
  have hh := CBox.mul_contains root70_contains root70_contains (c:=root140) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def mid141 : CBox := root140
lemma mid141_contains : mid141.Contains (rootPhase 140) := root140_contains
def root141 : CBox := ⟨⟨648514401022112445082935060369,648514401022112445085198343557⟩,⟨761202385484261814028594070986,761202385484261814031667064871⟩⟩
lemma root141_contains : root141.Contains (rootPhase 141) := by
  have hh := CBox.mul_contains mid141_contains root1_contains (c:=root141) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def root142 : CBox := ⟨⟨643831542889791465066440559809,643831542889791465068731682828⟩,⟨765167265622458925887687301195,765167265622458925890786010270⟩⟩
lemma root142_contains : root142.Contains (rootPhase 142) := by
  have hh := CBox.mul_contains root71_contains root71_contains (c:=root142) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def mid143 : CBox := root142
lemma mid143_contains : mid143.Contains (rootPhase 142) := root142_contains
def root143 : CBox := ⟨⟨639124444863775743799819575436,639124444863775743802144705396⟩,⟨769103337645579639345483895650,769103337645579639348609285817⟩⟩
lemma root143_contains : root143.Contains (rootPhase 143) := by
  have hh := CBox.mul_contains mid143_contains root1_contains (c:=root143) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def root144 : CBox := ⟨⟨634393284163645498213483773497,634393284163645498215835093094⟩,⟨773010453362736960809751837392,773010453362736960812902037787⟩⟩
lemma root144_contains : root144.Contains (rootPhase 144) := by
  have hh := CBox.mul_contains root72_contains root72_contains (c:=root144) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def mid145 : CBox := root144
lemma mid145_contains : mid145.Contains (rootPhase 144) := root144_contains
def root145 : CBox := ⟨⟨629638238914927025371270119997,629638238914927025373655913393⟩,⟨776888465673232450039659524093,776888465673232450042836590546⟩⟩
lemma root145_contains : root145.Contains (rootPhase 145) := by
  have hh := CBox.mul_contains mid145_contains root1_contains (c:=root145) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def root146 : CBox := ⟨⟨624859488142386377082341298131,624859488142386377084755366137⟩,⟨780737228572094478300406713374,780737228572094478303609776379⟩⟩
lemma root146_contains : root146.Contains (rootPhase 146) := by
  have hh := CBox.mul_contains root73_contains root73_contains (c:=root146) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def mid147 : CBox := root146
lemma mid147_contains : mid147.Contains (rootPhase 146) := root146_contains
def root147 : CBox := ⟨⟨620057211763289178644513024131,620057211763289178646962038872⟩,⟨784556597155575233022696898751,784556597155575233025927026529⟩⟩
lemma root147_contains : root147.Contains (rootPhase 147) := by
  have hh := CBox.mul_contains mid147_contains root1_contains (c:=root147) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def root148 : CBox := ⟨⟨615231590580626845483138743879,615231590580626845485614681942⟩,⟨788346427626606262007955950390,788346427626606262011211369956⟩⟩
lemma root148_contains : root148.Contains (rootPhase 148) := by
  have hh := CBox.mul_contains root74_contains root74_contains (c:=root148) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def mid149 : CBox := root148
lemma mid149_contains : mid149.Contains (rootPhase 148) := root148_contains
def root149 : CBox := ⟨⟨610382806276309452714553419848,610382806276309452717064772183⟩,⟨792106577300212351781120002051,792106577300212351784402677870⟩⟩
lemma root149_contains : root149.Contains (rootPhase 149) := by
  have hh := CBox.mul_contains mid149_contains root1_contains (c:=root149) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def root150 : CBox := ⟨⟨605511041404325513918807649869,605511041404325513921347682859⟩,⟨795836904608883536261555344868,795836904608883536264864300862⟩⟩
lemma root150_contains : root150.Contains (rootPhase 150) := by
  have hh := CBox.mul_contains root75_contains root75_contains (c:=root150) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def mid151 : CBox := root150
lemma mid151_contains : mid151.Contains (rootPhase 150) := root150_contains
def root151 : CBox := ⟨⟨600616479383868926652032427996,600616479383868926654608347662⟩,⟨799537269107905033498995317242,799537269107905033502331732774⟩⟩
lemma root151_contains : root151.Contains (rootPhase 151) := by
  have hh := CBox.mul_contains mid151_contains root1_contains (c:=root151) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def root152 : CBox := ⟨⟨595699304492433343465173431482,595699304492433343467776119239⟩,⟨803207531480644909805412326267,803207531480644909808773934206⟩⟩
lemma root152_contains : root152.Contains (rootPhase 152) := by
  have hh := CBox.mul_contains root76_contains root76_contains (c:=root152) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def mid153 : CBox := root152
lemma mid153_contains : mid153.Contains (rootPhase 152) := root152_contains
def root153 : CBox := ⟨⟨590759701858874228422000377014,590759701858874228424639416097⟩,⟨806847553543799272205235563188,806847553543799272208624823331⟩⟩
lemma root153_contains : root153.Contains (rootPhase 153) := by
  have hh := CBox.mul_contains mid153_contains root1_contains (c:=root153) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def root154 : CBox := ⟨⟨585797857456438860326172507514,585797857456438860328840604899⟩,⟨810457198252594791725410606451,810457198252594791728826428062⟩⟩
lemma root154_contains : root154.Contains (rootPhase 154) := by
  have hh := CBox.mul_contains root77_contains root77_contains (c:=root154) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def mid155 : CBox := root154
lemma mid155_contains : mid155.Contains (rootPhase 154) := root154_contains
def root155 : CBox := ⟨⟨580813958095764545073662247847,580813958095764545076367168362⟩,⟨814036329705948361653209072776,814036329705948361656652754364⟩⟩
lemma root155_contains : root155.Contains (rootPhase 155) := by
  have hh := CBox.mul_contains mid155_contains root1_contains (c:=root155) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def root156 : CBox := ⟨⟨575808191417845300744019427273,575808191417845300746751768012⟩,⟨817584813151583696503599516557,817584813151583696507068858095⟩⟩
lemma root156_contains : root156.Contains (rootPhase 156) := by
  have hh := CBox.mul_contains root78_contains root78_contains (c:=root156) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def mid157 : CBox := root156
lemma mid157_contains : mid157.Contains (rootPhase 156) := root156_contains
def root157 : CBox := ⟨⟨570780745886967280230674890173,570780745886967280233444519216⟩,⟨821102514991104679059094440909,821102514991104679062591841312⟩⟩
lemma root157_contains : root157.Contains (rootPhase 157) := by
  have hh := CBox.mul_contains mid157_contains root1_contains (c:=root157) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def root158 : CBox := ⟨⟨565731810783613197387766021768,565731810783613197390565056762⟩,⟨824589302785025264473452891488,824589302785025264476977135637⟩⟩
lemma root158_contains : root158.Contains (rootPhase 158) := by
  have hh := CBox.mul_contains root79_contains root79_contains (c:=root158) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def mid159 : CBox := root158
lemma mid159_contains : mid159.Contains (rootPhase 158) := root158_contains
def root159 : CBox := ⟨⟨560661576197336023837686031508,560661576197336023840522825999⟩,⟨828045045257755752066161504452,828045045257755752069714019657⟩⟩
lemma root159_contains : root159.Contains (rootPhase 159) := by
  have hh := CBox.mul_contains mid159_contains root1_contains (c:=root159) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def root160 : CBox := ⟨⟨555570233019602224740786797325,555570233019602224743650579537⟩,⟨831469612302545237077408433238,831469612302545237080986325143⟩⟩
lemma root160_contains : root160.Contains (rootPhase 160) := by
  have hh := CBox.mul_contains root80_contains root80_contains (c:=root160) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def mid161 : CBox := root160
lemma mid161_contains : mid161.Contains (rootPhase 160) := root160_contains
def root161 : CBox := ⟨⟨550457972936604802975220426149,550457972936604802978122428951⟩,⟨834862874986380056303005972934,834862874986380056306612334481⟩⟩
lemma root161_contains : root161.Contains (rootPhase 161) := by
  have hh := CBox.mul_contains mid161_contains root1_contains (c:=root161) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def root162 : CBox := ⟨⟨545324988422046422311896671415,545324988422046422314828398462⟩,⟨838224705554838043185586591473,838224705554838043189220074719⟩⟩
lemma root162_contains : root162.Contains (rootPhase 162) := by
  have hh := CBox.mul_contains root81_contains root81_contains (c:=root162) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def mid163 : CBox := root162
lemma mid163_contains : mid163.Contains (rootPhase 162) := root162_contains
def root163 : CBox := ⟨⟨540171472729892881295729103908,540171472729892881298699522046⟩,⟨841554977436898409602073556409,841554977436898409605735725817⟩⟩
lemma root163_contains : root163.Contains (rootPhase 163) := by
  have hh := CBox.mul_contains mid163_contains root1_contains (c:=root163) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def root164 : CBox := ⟨⟨534997619887097210660940280235,534997619887097210663938472993⟩,⟨844853565249707073258130827175,844853565249707073261818987992⟩⟩
lemma root164_contains : root164.Contains (rootPhase 164) := by
  have hh := CBox.mul_contains root82_contains root82_contains (c:=root164) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def mid165 : CBox := root164
lemma mid165_contains : mid165.Contains (rootPhase 164) := root164_contains
def root165 : CBox := ⟨⟨529803624686294668213892102599,529803624686294668216929448891⟩,⟨848120344803297251277677257323,848120344803297251281394310140⟩⟩
lemma root165_contains : root165.Contains (rootPhase 165) := by
  have hh := CBox.mul_contains mid165_contains root1_contains (c:=root165) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def root166 : CBox := ⟨⟨524589682678468906212914516571,524589682678468906215981874035⟩,⟨851355193105265142259818761257,851355193105265142263563214302⟩⟩
lemma root166_contains : root166.Contains (rootPhase 166) := by
  have hh := CBox.mul_contains root83_contains root83_contains (c:=root166) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def mid167 : CBox := root166
lemma mid167_contains : mid167.Contains (rootPhase 166) := root166_contains
def root167 : CBox := ⟨⟨519355990165589587359619794782,519355990165589587362726775584⟩,⟨854557988365400520766374560971,854557988365400520770148126795⟩⟩
lemma root167_contains : root167.Contains (rootPhase 167) := by
  have hh := CBox.mul_contains mid167_contains root1_contains (c:=root167) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def root168 : CBox := ⟨⟨514102744193221726591463659099,514102744193221726594597959259⟩,⟨857728610000272069900767741679,857728610000272069904567020887⟩⟩
lemma root168_contains : root168.Contains (rootPhase 168) := by
  have hh := CBox.mul_contains root84_contains root84_contains (c:=root168) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def mid169 : CBox := root168
lemma mid169_contains : mid169.Contains (rootPhase 168) := root168_contains
def root169 : CBox := ⟨⟨508830142543107036929492716699,508830142543107036932667098531⟩,⟨860866938637767279343065240434,860866938637767279346893838032⟩⟩
lemma root169_contains : root169.Contains (rootPhase 169) := by
  have hh := CBox.mul_contains mid169_contains root1_contains (c:=root169) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def root170 : CBox := ⟨⟨503538383725717558689588939299,503538383725717558692793588800⟩,⟨863972856121586737916612783199,863972856121586737920469054249⟩⟩
lemma root170_contains : root170.Contains (rootPhase 170) := by
  have hh := CBox.mul_contains root85_contains root85_contains (c:=root170) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def mid171 : CBox := root170
lemma mid171_contains : mid171.Contains (rootPhase 170) := root170_contains
def root171 : CBox := ⟨⟨498227666972781852408679068588,498227666972781852411924268785⟩,⟨867046245515692651478644725006,867046245515692651482530539390⟩⟩
lemma root171_contains : root171.Contains (rootPhase 171) := by
  have hh := CBox.mul_contains mid171_contains root1_contains (c:=root171) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def root172 : CBox := ⟨⟨492898192229784036870701501671,492898192229784036873974682683⟩,⟨870086991108711418650726435028,870086991108711418654638528561⟩⟩
lemma root172_contains : root172.Contains (rootPhase 172) := by
  have hh := CBox.mul_contains root86_contains root86_contains (c:=root172) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def mid173 : CBox := root172
lemma mid173_contains : mid173.Contains (rootPhase 172) := root172_contains
def root173 : CBox := ⟨⟨487550160148435954639132937391,487550160148435954642447128429⟩,⟨873094978418290098634503136595,873094978418290098638444985775⟩⟩
lemma root173_contains : root173.Contains (rootPhase 173) := by
  have hh := CBox.mul_contains mid173_contains root1_contains (c:=root173) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def root174 : CBox := ⟨⟨482183772079122748514970745873,482183772079122748518315428569⟩,⟨876070094195406607094245405790,876070094195406607098215200712⟩⟩
lemma root174_contains : root174.Contains (rootPhase 174) := by
  have hh := CBox.mul_contains root87_contains root87_contains (c:=root174) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def mid175 : CBox := root174
lemma mid175_contains : mid175.Contains (rootPhase 174) := root174_contains
def root175 : CBox := ⟨⟨476799230063322133339757243362,476799230063322133343143404317⟩,⟨879012226428633477829707738949,879012226428633477833707518552⟩⟩
lemma root175_contains : root175.Contains (rootPhase 175) := by
  have hh := CBox.mul_contains mid175_contains root1_contains (c:=root175) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def root176 : CBox := ⟨⟨471396736825997648553966749491,471396736825997648557380114627⟩,⟨881921264348355029711125828589,881921264348355029715151372056⟩⟩
lemma root176_contains : root176.Contains (rootPhase 176) := by
  have hh := CBox.mul_contains root88_contains root88_contains (c:=root176) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def mid177 : CBox := root176
lemma mid177_contains : mid177.Contains (rootPhase 176) := root176_contains
def root177 : CBox := ⟨⟨465976495767966177900307822487,465976495767966177903763119598⟩,⟨884797098430937780102358662627,884797098430937780106414401112⟩⟩
lemma root177_contains : root177.Contains (rootPhase 177) := by
  have hh := CBox.mul_contains mid177_contains root1_contains (c:=root177) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def root178 : CBox := ⟨⟨460538710958240023630711502930,460538710958240023634197484501⟩,⟨887639620402853947758516824328,887639620402853947762600773428⟩⟩
lemma root178_contains : root178.Contains (rootPhase 178) := by
  have hh := CBox.mul_contains root89_contains root89_contains (c:=root178) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def mid179 : CBox := root178
lemma mid179_contains : mid179.Contains (rootPhase 178) := root178_contains
def root179 : CBox := ⟨⟨455083587126343823533371686614,455083587126343823536900067501⟩,⟨890448723244757889950468179058,890448723244757889954582556196⟩⟩
lemma root179_contains : root179.Contains (rootPhase 179) := by
  have hh := CBox.mul_contains mid179_contains root1_contains (c:=root179) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def root180 : CBox := ⟨⟨449611329654606600043776584555,449611329654606600047333000821⟩,⟨893224301195515320340718370894,893224301195515320344859262834⟩⟩
lemma root180_contains : root180.Contains (rootPhase 180) := by
  have hh := CBox.mul_contains root90_contains root90_contains (c:=root180) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def mid181 : CBox := root180
lemma mid181_contains : mid181.Contains (rootPhase 180) := root180_contains
def root181 : CBox := ⟨⟨444122144570429231639523602132,444122144570429231643122873499⟩,⟨895966249756185155912844379412,895966249756185155917015917678⟩⟩
lemma root181_contains : root181.Contains (rootPhase 181) := by
  have hh := CBox.mul_contains mid181_contains root1_contains (c:=root181) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def root182 : CBox := ⟨⟨438616238538527637644458109572,438616238538527637648088224353⟩,⟨898674465693953843040244036798,898674465693953843044444049202⟩⟩
lemma root182_contains : root182.Contains (rootPhase 182) := by
  have hh := CBox.mul_contains root91_contains root91_contains (c:=root182) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def mid183 : CBox := root182
lemma mid183_contains : mid183.Contains (rootPhase 182) := root182_contains
def root183 : CBox := ⟨⟨433093818853151968481626962894,433093818853151968485300399223⟩,⟨901348847046022014568995312888,901348847046022014573226208551⟩⟩
lemma root183_contains : root183.Contains (rootPhase 183) := by
  have hh := CBox.mul_contains mid183_contains root1_contains (c:=root183) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def root184 : CBox := ⟨⟨427555093430282094318351180010,427555093430282094322051853446⟩,⟨903989293123443331584433820345,903989293123443331588690715874⟩⟩
lemma root184_contains : root184.Contains (rootPhase 184) := by
  have hh := CBox.mul_contains root92_contains root92_contains (c:=root184) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def mid185 : CBox := root184
lemma mid185_contains : mid185.Contains (rootPhase 184) := root184_contains
def root185 : CBox := ⟨⟨422000270799799685938644000562,422000270799799685942388445672⟩,⟨906595704514915365331175800529,906595704514915365335463795718⟩⟩
lemma root185_contains : root185.Contains (rootPhase 185) := by
  have hh := CBox.mul_contains mid185_contains root1_contains (c:=root185) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def root186 : CBox := ⟨⟨416429560097637182559933112071,416429560097637182563708527423⟩,⟨909167983090522376562082809300,909167983090522376566399533728⟩⟩
lemma root186_contains : root186.Contains (rootPhase 186) := by
  have hh := CBox.mul_contains root93_contains root93_contains (c:=root186) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def mid187 : CBox := root186
lemma mid187_contains : mid187.Contains (rootPhase 186) := root186_contains
def root187 : CBox := ⟨⟨410843171057903942180772390601,410843171057903942184592043080⟩,⟨911706032005429851402576785821,911706032005429851406924850647⟩⟩
lemma root187_contains : root187.Contains (rootPhase 187) := by
  have hh := CBox.mul_contains mid187_contains root1_contains (c:=root187) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def root188 : CBox := ⟨⟨405241314004989870905766693899,405241314004989870909614279517⟩,⟨914209755703530654633177989187,914209755703530654637552745042⟩⟩
lemma root188_contains : root188.Contains (rootPhase 188) := by
  have hh := CBox.mul_contains root94_contains root94_contains (c:=root188) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def mid189 : CBox := root188
lemma mid189_contains : mid189.Contains (rootPhase 188) := root188_contains
def root189 : CBox := ⟨⟨399624199845646828541373720862,399624199845646828545265995395⟩,⟨916679059921042663114601370883,916679059921042663119007690884⟩⟩
lemma root189_contains : root189.Contains (rootPhase 189) := by
  have hh := CBox.mul_contains mid189_contains root1_contains (c:=root189) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def root190 : CBox := ⟨⟨393992040061048108593423473549,393992040061048108597346810268⟩,⟨919113851690057743906604571031,919113851690057743911039872420⟩⟩
lemma root190_contains : root190.Contains (rootPhase 190) := by
  have hh := CBox.mul_contains root95_contains root95_contains (c:=root190) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def mid191 : CBox := root190
lemma mid191_contains : mid191.Contains (rootPhase 190) := root190_contains
def root191 : CBox := ⟨⟨388345046698826291622199438285,388345046698826291626167928368⟩,⟨921514039342041943463504058951,921514039342041943467971168949⟩⟩
lemma root191_contains : root191.Contains (rootPhase 191) := by
  have hh := CBox.mul_contains mid191_contains root1_contains (c:=root191) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def root192 : CBox := ⟨⟨382683432365089771725646206177,382683432365089771729641387663⟩,⟨923879532511286756126274795439,923879532511286756130767718450⟩⟩
lemma root192_contains : root192.Contains (rootPhase 192) := by
  have hh := CBox.mul_contains root96_contains root96_contains (c:=root192) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def mid193 : CBox := root192
lemma mid193_contains : mid193.Contains (rootPhase 192) := root192_contains
def root193 : CBox := ⟨⟨377007410216418256723724926052,377007410216418256727765704771⟩,⟨926210242138311341972865700747,926210242138311341977390651738⟩⟩
lemma root193_contains : root193.Contains (rootPhase 193) := by
  have hh := CBox.mul_contains mid193_contains root1_contains (c:=root193) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def root194 : CBox := ⟨⟨371317193951837543409070198108,371317193951837543413142098365⟩,⟨928506080473215565935221752024,928506080473215565939775925727⟩⟩
lemma root194_contains : root194.Contains (rootPhase 194) := by
  have hh := CBox.mul_contains root97_contains root97_contains (c:=root194) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def mid195 : CBox := root194
lemma mid195_contains : mid195.Contains (rootPhase 194) := root194_contains
def root195 : CBox := ⟨⟨365612997804773870008851808658,365612997804773870012969769466⟩,⟨930766961078983731942907148556,930766961078983731947493598303⟩⟩
lemma root195_contains : root195.Contains (rootPhase 195) := by
  have hh := CBox.mul_contains mid195_contains root1_contains (c:=root195) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def root196 : CBox := ⟨⟨359895036534988148772190346399,359895036534988148776335979240⟩,⟨932992798834738887709678190143,932992798834738887714291439244⟩⟩
lemma root196_contains : root196.Contains (rootPhase 196) := by
  have hh := CBox.mul_contains root98_contains root98_contains (c:=root196) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def mid197 : CBox := root196
lemma mid197_contains : mid197.Contains (rootPhase 196) := root196_contains
def root197 : CBox := ⟨⟨354163525420490382354452037688,354163525420490382358644178368⟩,⟨935183509938947577640205622625,935183509938947577644851376442⟩⟩
lemma root197_contains : root197.Contains (rootPhase 197) := by
  have hh := CBox.mul_contains mid197_contains root1_contains (c:=root197) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def root198 : CBox := ⟨⟨348418680249434568416342990242,348418680249434568420566275554⟩,⟨937339011912574923199879401562,937339011912574923204554616262⟩⟩
lemma root198_contains : root198.Contains (rootPhase 198) := by
  have hh := CBox.mul_contains root99_contains root99_contains (c:=root198) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def mid199 : CBox := root198
lemma mid199_contains : mid199.Contains (rootPhase 198) := root198_contains
def root199 : CBox := ⟨⟨342660717311994397589786645884,342660717311994397594056901229⟩,⟨939459223602189911960629006778,939459223602189911965336977786⟩⟩
lemma root199_contains : root199.Contains (rootPhase 199) := by
  have hh := CBox.mul_contains mid199_contains root1_contains (c:=root199) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def root200 : CBox := ⟨⟨336889853392220050686238391556,336889853392220050690535133334⟩,⟨941544065183020778410452438066,941544065183020778415186391982⟩⟩
lemma root200_contains : root200.Contains (rootPhase 200) := by
  have hh := CBox.mul_contains root100_contains root100_contains (c:=root200) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def mid201 : CBox := root200
lemma mid201_contains : mid201.Contains (rootPhase 200) := root200_contains
def root201 : CBox := ⟨⟨331106305759876401734145983761,331106305759876401738490135283⟩,⟨943593458161960361493224191436,943593458161960361497991126523⟩⟩
lemma root201_contains : root201.Contains (rootPhase 201) := by
  have hh := CBox.mul_contains mid201_contains root1_contains (c:=root201) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def root202 : CBox := ⟨⟨325310292162262934132888173961,325310292162262934137263459758⟩,⟨945607325380521325728849425227,945607325380521325733646047758⟩⟩
lemma root202_contains : root202.Contains (rootPhase 202) := by
  have hh := CBox.mul_contains root101_contains root101_contains (c:=root202) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def mid203 : CBox := root202
lemma mid203_contains : mid203.Contains (rootPhase 202) := root202_contains
def root203 : CBox := ⟨⟨319502030816015677898421603452,319502030816015677902844759942⟩,⟨947585591017741134651270813442,947585591017741134656100672140⟩⟩
lemma root203_contains : root203.Contains (rootPhase 203) := by
  have hh := CBox.mul_contains mid203_contains root1_contains (c:=root203) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def root204 : CBox := ⟨⟨313681740398891476653362371090,313681740398891476657812774402⟩,⟨949528180593036667193802157119,949528180593036667198658848075⟩⟩
lemma root204_contains : root204.Contains (rootPhase 204) := by
  have hh := CBox.mul_contains root102_contains root102_contains (c:=root204) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def mid205 : CBox := root204
lemma mid205_contains : mid205.Contains (rootPhase 204) := root204_contains
def root205 : CBox := ⟨⟨307849640041534893678916846613,307849640041534893683415562886⟩,⟨951435020969008369547020859430,951435020969008369551911019596⟩⟩
lemma root205_contains : root205.Contains (rootPhase 205) := by
  have hh := CBox.mul_contains mid205_contains root1_contains (c:=root205) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def root206 : CBox := ⟨⟨302005949319228067000294738230,302005949319228067004824541306⟩,⟨953306040354193836914566596233,953306040354193836919486665348⟩⟩
lemma root206_contains : root206.Contains (rootPhase 206) := by
  have hh := CBox.mul_contains root103_contains root103_contains (c:=root206) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def mid207 : CBox := root206
lemma mid207_contains : mid207.Contains (rootPhase 206) := root206_contains
def root207 : CBox := ⟨⟨296150888243623824118587113764,296150888243623824123165689497⟩,⟨955141168305770721495962874955,955141168305770721500916671595⟩⟩
lemma root207_contains : root207.Contains (rootPhase 207) := by
  have hh := CBox.mul_contains mid207_contains root1_contains (c:=root207) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def root208 : CBox := ⟨⟨290284677254462367632974456748,290284677254462367637578609267⟩,⟨956940335732208864933586002103,956940335732208864938565390423⟩⟩
lemma root208_contains : root208.Contains (rootPhase 208) := by
  have hh := CBox.mul_contains root104_contains root104_contains (c:=root208) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def mid209 : CBox := root208
lemma mid209_contains : mid209.Contains (rootPhase 208) := root208_contains
def root209 : CBox := ⟨⟨284407537211271843615061994936,284407537211271843619715352187⟩,⟨958703474895871555372412613723,958703474895871555377425956065⟩⟩
lemma root209_contains : root209.Contains (rootPhase 209) := by
  have hh := CBox.mul_contains mid209_contains root1_contains (c:=root209) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def root210 : CBox := ⟨⟨278519689385053105204578323200,278519689385053105209262686125⟩,⟨960430519415565811196782520793,960430519415565811201825979597⟩⟩
lemma root210_contains : root210.Contains (rootPhase 210) := by
  have hh := CBox.mul_contains root105_contains root105_contains (c:=root210) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def mid211 : CBox := root210
lemma mid211_contains : mid211.Contains (rootPhase 210) := root210_contains
def root211 : CBox := ⟨⟨272621355449948984490046382318,272621355449948984494780408271⟩,⟨962121404269041595427330146660,962121404269041595432407820982⟩⟩
lemma root211_contains : root211.Contains (rootPhase 211) := by
  have hh := CBox.mul_contains mid211_contains root1_contains (c:=root211) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def root212 : CBox := ⟨⟨266712757474898386321966050773,266712757474898386326726733607⟩,⟨963776065795439866684172286002,963776065795439866689276741720⟩⟩
lemma root212_contains : root212.Contains (rootPhase 212) := by
  have hh := CBox.mul_contains root106_contains root106_contains (c:=root212) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def mid213 : CBox := root212
lemma mid213_contains : mid213.Contains (rootPhase 212) := root212_contains
def root213 : CBox := ⟨⟨260794117915275518276834974296,260794117915275518281645756835⟩,⟨965394441697689374548529988376,965394441697689374553668896456⟩⟩
lemma root213_contains : root213.Contains (rootPhase 213) := by
  have hh := CBox.mul_contains mid213_contains root1_contains (c:=root213) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def root214 : CBox := ⟨⟨254865659604514571550607801310,254865659604514571555449469908⟩,⟨966976471044852109084886559891,966976471044852109090055786603⟩⟩
lemma root214_contains : root214.Contains (rootPhase 214) := by
  have hh := CBox.mul_contains root107_contains root107_contains (c:=root214) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def mid215 : CBox := root214
lemma mid215_contains : mid215.Contains (rootPhase 214) := root214_contains
def root215 : CBox := ⟨⟨248927605745720168107278582214,248927605745720168112170807423⟩,⟨968522094274417316218732602822,968522094274417316223936546493⟩⟩
lemma root215_contains : root215.Contains (rootPhase 215) := by
  have hh := CBox.mul_contains mid215_contains root1_contains (c:=root215) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def root216 : CBox := ⟨⟨242980179903263889944851452594,242980179903263889949768716212⟩,⟨970031253194543992601610918971,970031253194543992606840455762⟩⟩
lemma root216_contains : root216.Contains (rootPhase 216) := by
  have hh := CBox.mul_contains root108_contains root108_contains (c:=root216) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def mid217 : CBox := root216
lemma mid217_contains : mid217.Contains (rootPhase 216) := root216_contains
def root217 : CBox := ⟨⟨237023605994367206864281779696,237023605994367206869250026710⟩,⟨971503890986251775534704030163,971503890986251775539968514749⟩⟩
lemma root217_contains : root217.Contains (rootPhase 217) := by
  have hh := CBox.mul_contains mid217_contains root1_contains (c:=root217) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def root218 : CBox := ⟨⟨231058108280671119639760607105,231058108280671119644759586191⟩,⟨972939952205560145465304376006,972939952205560145470599366596⟩⟩
lemma root218_contains : root218.Contains (rootPhase 218) := by
  have hh := CBox.mul_contains root109_contains root109_contains (c:=root218) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def mid219 : CBox := root218
lemma mid219_contains : mid219.Contains (rootPhase 218) := root218_contains
def root219 : CBox := ⟨⟨225083911359792835988135102302,225083911359792835993185520155⟩,⟨974339382785575860516283365732,974339382785575860521613571676⟩⟩
lemma root219_contains : root219.Contains (rootPhase 219) := by
  have hh := CBox.mul_contains mid219_contains root1_contains (c:=root219) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def root220 : CBox := ⟨⟨219101240156869797224211718623,219101240156869797229288033991⟩,⟨975702130038528544457939124040,975702130038528544463295968932⟩⟩
lemma root220_contains : root220.Contains (rootPhase 220) := by
  have hh := CBox.mul_contains root110_contains root110_contains (c:=root220) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def mid221 : CBox := root220
lemma mid221_contains : mid221.Contains (rootPhase 220) := root220_contains
def root221 : CBox := ⟨⟨213110319916091373964199916604,213110319916091373969328101238⟩,⟨977028142657754351483386757114,977028142657754351488779057418⟩⟩
lemma root221_contains : root221.Contains (rootPhase 221) := by
  have hh := CBox.mul_contains mid221_contains root1_contains (c:=root221) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def root222 : CBox := ⟨⟨207111376192218549704537336739,207111376192218549709696060239⟩,⟨978317370719627633103740152659,978317370719627633109163139070⟩⟩
lemma root222_contains : root222.Contains (rootPhase 222) := by
  have hh := CBox.mul_contains root111_contains root111_contains (c:=root222) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def mid223 : CBox := root222
lemma mid223_contains : mid223.Contains (rootPhase 222) := root222_contains
def root223 : CBox := ⟨⟨201104634842091911554832914846,201104634842091911560043961447⟩,⟨979569765685440534436803092303,979569765685440534442261804560⟩⟩
lemma root223_contains : root223.Contains (rootPhase 223) := by
  have hh := CBox.mul_contains mid223_contains root1_contains (c:=root223) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def root224 : CBox := ⟨⟨195090322016128267844656667271,195090322016128267849891334285⟩,⟨980785280403230449123641526664,980785280403230449129125075683⟩⟩
lemma root224_contains : root224.Contains (rootPhase 224) := by
  have hh := CBox.mul_contains root112_contains root112_contains (c:=root224) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def mid225 : CBox := root224
lemma mid225_contains : mid225.Contains (rootPhase 224) := root224_contains
def root225 : CBox := ⟨⟨189068664149806212751337533003,189068664149806212756624939959⟩,⟨981963869109555264070284129869,981963869109555264075803634977⟩⟩
lemma root225_contains : root225.Contains (rootPhase 225) := by
  have hh := CBox.mul_contains mid225_contains root1_contains (c:=root225) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def root226 : CBox := ⟨⟨183039887955140958512851413323,183039887955140958518169131799⟩,⟨983105487431216327177716307029,983105487431216327183266660976⟩⟩
lemma root226_contains : root226.Contains (rootPhase 226) := by
  have hh := CBox.mul_contains root113_contains root113_contains (c:=root226) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def mid227 : CBox := root226
lemma mid227_contains : mid227.Contains (rootPhase 226) := root226_contains
def root227 : CBox := ⟨⟨177004220412148756193126405591,177004220412148756198497316128⟩,⟨984210092386929073191265963037,984210092386929073196852546219⟩⟩
lemma root227_contains : root227.Contains (rootPhase 227) := by
  have hh := CBox.mul_contains mid227_contains root1_contains (c:=root227) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def root228 : CBox := ⟨⟨170961888760301226359910785477,170961888760301226365306665908⟩,⟨985277642388941244771391285946,985277642388941244777004266241⟩⟩
lemma root228_contains : root228.Contains (rootPhase 228) := by
  have hh := CBox.mul_contains root114_contains root114_contains (c:=root228) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def mid229 : CBox := root228
lemma mid229_contains : mid229.Contains (rootPhase 228) := root228_contains
def root229 : CBox := ⟨⟨164913120489969921414425114503,164913120489969921419874610670⟩,⟨986308097244598647860646554283,986308097244598647866296006479⟩⟩
lemma root229_contains : root229.Contains (rootPhase 229) := by
  have hh := CBox.mul_contains mid229_contains root1_contains (c:=root229) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def root230 : CBox := ⟨⟨158858143333861441680600749787,158858143333861441686080289390⟩,⟨987301418157858382397143680607,987301418157858382402824137007⟩⟩
lemma root230_contains : root230.Contains (rootPhase 230) := by
  have hh := CBox.mul_contains root115_contains root115_contains (c:=root230) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def mid231 : CBox := root230
lemma mid231_contains : mid231.Contains (rootPhase 230) := root230_contains
def root231 : CBox := ⟨⟨152797185258443427716519410598,152797185258443427722053016363⟩,⟨988257567730749491402096332101,988257567730749491407813536184⟩⟩
lemma root231_contains : root231.Contains (rootPhase 231) := by
  have hh := CBox.mul_contains mid231_contains root1_contains (c:=root231) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def root232 : CBox := ⟨⟨146730474455361751655015963461,146730474455361751660572441549⟩,⟨989176509964780973448959377619,989176509964780973454701343827⟩⟩
lemma root232_contains : root232.Contains (rootPhase 232) := by
  have hh := CBox.mul_contains root116_contains root116_contains (c:=root232) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def mid233 : CBox := root232
lemma mid233_contains : mid233.Contains (rootPhase 232) := root232_contains
def root233 : CBox := ⟨⟨140658239332849230710921945015,140658239332849230716532900300⟩,⟨990058210262297105503167778303,990058210262297105508946726365⟩⟩
lemma root233_contains : root233.Contains (rootPhase 233) := by
  have hh := CBox.mul_contains mid233_contains root1_contains (c:=root233) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def root234 : CBox := ⟨⟨134580708507126186312471173014,134580708507126186318111868817⟩,⟨990902635427780025105476857109,990902635427780025111286946850⟩⟩
lemma root234_contains : root234.Contains (rootPhase 234) := by
  have hh := CBox.mul_contains root117_contains root117_contains (c:=root234) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def mid235 : CBox := root234
lemma mid235_contains : mid235.Contains (rootPhase 234) := root234_contains
def root235 : CBox := ⟨⟨128498110793793172620495458032,128498110793793172626191079598⟩,⟨991709753669099522857265189800,991709753669099522863112539654⟩⟩
lemma root235_contains : root235.Contains (rootPhase 235) := by
  have hh := CBox.mul_contains mid235_contains root1_contains (c:=root235) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def root236 : CBox := ⟨⟨122410675199216198494767009747,122410675199216198500486500036⟩,⟨992479534598709998153963467479,992479534598709998159836864993⟩⟩
lemma root236_contains : root236.Contains (rootPhase 236) := by
  have hh := CBox.mul_contains root118_contains root118_contains (c:=root236) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def mid237 : CBox := root236
lemma mid237_contains : mid237.Contains (rootPhase 236) := root236_contains
def root237 : CBox := ⟨⟨116318630911904767248573818848,116318630911904767254348651099⟩,⟨993211949234794533101772395429,993211949234794533107683297714⟩⟩
lemma root237_contains : root237.Contains (rootPhase 237) := by
  have hh := CBox.mul_contains mid237_contains root1_contains (c:=root237) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def root238 : CBox := ⟨⟨110222207293883058803908610374,110222207293883058809712839009⟩,⟨993906970002356041544072420854,993906970002356041550014592691⟩⟩
lemma root238_contains : root238.Contains (rootPhase 238) := by
  have hh := CBox.mul_contains root119_contains root119_contains (c:=root238) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def mid239 : CBox := root238
lemma mid239_contains : mid239.Contains (rootPhase 238) := root238_contains
def root239 : CBox := ⟨⟨104121633872054579116920159611,104121633872054579122780176916⟩,⟨994564570734255452116230756668,994564570734255452122210713922⟩⟩
lemma root239_contains : root239.Contains (rootPhase 239) := by
  have hh := CBox.mul_contains mid239_contains root1_contains (c:=root239) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def root240 : CBox := ⟨⟨98017140329560601990156046835,98017140329560601996037135398⟩,⟨995184726672196886241943339603,995184726672196886247947026245⟩⟩
lemma root240_contains : root240.Contains (rootPhase 240) := by
  have hh := CBox.mul_contains root120_contains root120_contains (c:=root240) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def mid241 : CBox := root240
lemma mid241_contains : mid241.Contains (rootPhase 240) := root240_contains
def root241 : CBox := ⟨⟨91908956497132728620918142865,91908956497132728626855419482⟩,⟨995767414467659793979576697897,995767414467659793985618402054⟩⟩
lemma root241_contains : root241.Contains (rootPhase 241) := by
  have hh := CBox.mul_contains mid241_contains root1_contains (c:=root241) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def root242 : CBox := ⟨⟨85797312344439890457463798187,85797312344439890463430092802⟩,⟨996312612182778012624285174045,996312612182778012630358255377⟩⟩
lemma root242_contains : root242.Contains (rootPhase 242) := by
  have hh := CBox.mul_contains root121_contains root121_contains (c:=root242) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def mid243 : CBox := root242
lemma mid243_contains : mid243.Contains (rootPhase 242) := root242_contains
def root243 : CBox := ⟨⟨79682437971430121142994653861,79682437971430121149017581176⟩,⟨996820299291165714969662790265,996820299291165714975774171964⟩⟩
lemma root243_contains : root243.Contains (rootPhase 243) := by
  have hh := CBox.mul_contains mid243_contains root1_contains (c:=root243) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def root244 : CBox := ⟨⟨73564563599667423525323206549,73564563599667423531368730922⟩,⟨997290456678690216132611238394,997290456678690216138748203692⟩⟩
lemma root244_contains : root244.Contains (rootPhase 244) := by
  have hh := CBox.mul_contains root122_contains root122_contains (c:=root244) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def mid245 : CBox := root244
lemma mid245_contains : mid245.Contains (rootPhase 244) := root244_contains
def root245 : CBox := ⟨⟨67443919563664057893796410131,67443919563664057899898975216⟩,⟨997723066644191609845534992118,997723066644191609851710503798⟩⟩
lemma root245_contains : root245.Contains (rootPhase 245) := by
  have hh := CBox.mul_contains mid245_contains root1_contains (c:=root245) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def root246 : CBox := ⟨⟨61320736302208577778419244939,61320736302208577784550406847⟩,⟨998118112900149207122121766392,998118112900149207128328752975⟩⟩
lemma root246_contains : root246.Contains (rootPhase 246) := by
  have hh := CBox.mul_contains root123_contains root123_contains (c:=root246) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def mid247 : CBox := root246
lemma mid247_contains : mid247.Contains (rootPhase 246) := root246_contains
def root247 : CBox := ⟨⟨55195244349689939805218437307,55195244349689939811407082540⟩,⟨998475580573294752205498848952,998475580573294752211744666898⟩⟩
lemma root247_contains : root247.Contains (rootPhase 247) := by
  have hh := CBox.mul_contains mid247_contains root1_contains (c:=root247) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def root248 : CBox := ⟨⟨49067674327418014250710942697,49067674327418014256919561359⟩,⟨998795456205172392711692965402,998795456205172392717962206623⟩⟩
lemma root248_contains : root248.Contains (rootPhase 248) := by
  have hh := CBox.mul_contains root124_contains root124_contains (c:=root248) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def mid249 : CBox := root248
lemma mid249_contains : mid249.Contains (rootPhase 248) := root248_contains
def root249 : CBox := ⟨⟨42938256934940823072846649284,42938256934940823079113143444⟩,⟨999077727752645382885677027714,999077727752645382891985335028⟩⟩
lemma root249_contains : root249.Contains (rootPhase 249) := by
  have hh := CBox.mul_contains mid249_contains root1_contains (c:=root249) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def root250 : CBox := ⟨⟨36807222941358832320035851176,36807222941358832326330486180⟩,⟨999322384588349500893093411062,999322384588349500899433270211⟩⟩
lemma root250_contains : root250.Contains (rootPhase 250) := by
  have hh := CBox.mul_contains root125_contains root125_contains (c:=root250) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def mid251 : CBox := root250
lemma mid251_contains : mid251.Contains (rootPhase 250) := root250_contains
def root251 : CBox := ⟨⟨30674803176636625929690192739,30674803176636625936043143629⟩,⟨999529417501093163076549132537,999529417501093163082928344708⟩⟩
lemma root251_contains : root251.Contains (rootPhase 251) := by
  have hh := CBox.mul_contains mid251_contains root1_contains (c:=root251) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def root252 : CBox := ⟨⟨24541228522912288027388324195,24541228522912288033762425160⟩,⟨999698818696204220112591991068,999698818696204220118996199589⟩⟩
lemma root252_contains : root252.Contains (rootPhase 252) := by
  have hh := CBox.mul_contains root126_contains root126_contains (c:=root252) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def mid253 : CBox := root252
lemma mid253_contains : mid253.Contains (rootPhase 252) := root252_contains
def root253 : CBox := ⟨⟨18406729905804820922985997109,18406729905804820929418813066⟩,⟨999830581795823422012521788128,999830581795823422018965596398⟩⟩
lemma root253_contains : root253.Contains (rootPhase 253) := by
  have hh := CBox.mul_contains mid253_contains root1_contains (c:=root253) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def root254 : CBox := ⟨⟨12271538285719926075009414806,12271538285719926081469872514⟩,⟨999924701839144540918423110472,999924701839144540924898535435⟩⟩
lemma root254_contains : root254.Contains (rootPhase 254) := by
  have hh := CBox.mul_contains root127_contains root127_contains (c:=root254) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def mid255 : CBox := root254
lemma mid255_contains : mid255.Contains (rootPhase 254) := root254_contains
def root255 : CBox := ⟨⟨6135884649154475355207143807,6135884649154475361726754676⟩,⟨999981175282601142653739970152,999981175282601142660255283651⟩⟩
lemma root255_contains : root255.Contains (rootPhase 255) := by
  have hh := CBox.mul_contains mid255_contains root1_contains (c:=root255) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def root256 : CBox := ⟨⟨(-4446491810),2090674626⟩,⟨999999999999999999996731406635,1000000000000000000003268573071⟩⟩
lemma root256_contains : root256.Contains (rootPhase 256) := by
  have hh := CBox.mul_contains root128_contains root128_contains (c:=root256) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def mid257 : CBox := root256
lemma mid257_contains : mid257.Contains (rootPhase 256) := root256_contains
def root257 : CBox := ⟨⟨(-6135884649154475364121070499),(-6135884649154475357524373631)⟩,⟨999981175282601142653694529457,999981175282601142660271814140⟩⟩
lemma root257_contains : root257.Contains (rootPhase 257) := by
  have hh := CBox.mul_contains mid257_contains root1_contains (c:=root257) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def root258 : CBox := ⟨⟨(-12271538285719926083907186437),(-12271538285719926077283380445)⟩,⟨999924701839144540918327441768,999924701839144540924936384819⟩⟩
lemma root258_contains : root258.Contains (rootPhase 258) := by
  have hh := CBox.mul_contains root129_contains root129_contains (c:=root258) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def mid259 : CBox := root258
lemma mid259_contains : mid259.Contains (rootPhase 258) := root258_contains
def root259 : CBox := ⟨⟨(-18406729905804820931899710801),(-18406729905804820925215935471)⟩,⟨999830581795823422012375413455,999830581795823422019025244815⟩⟩
lemma root259_contains : root259.Contains (rootPhase 259) := by
  have hh := CBox.mul_contains mid259_contains root1_contains (c:=root259) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def root260 : CBox := ⟨⟨(-24541228522912288036282135069),(-24541228522912288029578829556)⟩,⟨999698818696204220112399464241,999698818696204220119073096486⟩⟩
lemma root260_contains : root260.Contains (rootPhase 260) := by
  have hh := CBox.mul_contains root130_contains root130_contains (c:=root260) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def mid261 : CBox := root260
lemma mid261_contains : mid261.Contains (rootPhase 260) := root260_contains
def root261 : CBox := ⟨⟨(-30674803176636625938603210468),(-30674803176636625931839543007)⟩,⟨999529417501093163076308850556,999529417501093163083024097439⟩⟩
lemma root261_contains : root261.Contains (rootPhase 261) := by
  have hh := CBox.mul_contains mid261_contains root1_contains (c:=root261) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def root262 : CBox := ⟨⟨(-36807222941358832328932485752),(-36807222941358832322142293237)⟩,⟨999322384588349500892803641331,999322384588349500899549616816⟩⟩
lemma root262_contains : root262.Contains (rootPhase 262) := by
  have hh := CBox.mul_contains root131_contains root131_contains (c:=root262) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def mid263 : CBox := root262
lemma mid263_contains : mid263.Contains (rootPhase 262) := root262_contains
def root263 : CBox := ⟨⟨(-42938256934940823081759036285),(-42938256934940823074908045330)⟩,⟨999077727752645382885335845362,999077727752645382892124206907⟩⟩
lemma root263_contains : root263.Contains (rootPhase 263) := by
  have hh := CBox.mul_contains mid263_contains root1_contains (c:=root263) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def root264 : CBox := ⟨⟨(-49067674327418014259601890697),(-49067674327418014252734572266)⟩,⟨998795456205172392711307772142,998795456205172392718116209681⟩⟩
lemma root264_contains : root264.Contains (rootPhase 264) := by
  have hh := CBox.mul_contains root132_contains root132_contains (c:=root264) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def mid265 : CBox := root264
lemma mid265_contains : mid265.Contains (rootPhase 264) := root264_contains
def root265 : CBox := ⟨⟨(-55195244349689939814129230791),(-55195244349689939807200740815)⟩,⟨998475580573294752205065959713,998475580573294752211917494900⟩⟩
lemma root265_contains : root265.Contains (rootPhase 265) := by
  have hh := CBox.mul_contains mid265_contains root1_contains (c:=root265) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def root266 : CBox := ⟨⟨(-61320736302208577787313407998),(-61320736302208577780359011273)⟩,⟨998118112900149207121640142853,998118112900149207128521454041⟩⟩
lemma root266_contains : root266.Contains (rootPhase 266) := by
  have hh := CBox.mul_contains root133_contains root133_contains (c:=root266) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def mid267 : CBox := root266
lemma mid267_contains : mid267.Contains (rootPhase 266) := root266_contains
def root267 : CBox := ⟨⟨(-67443919563664057902706146815),(-67443919563664057895690144684)⟩,⟨997723066644191609845001270978,997723066644191609851926452108⟩⟩
lemma root267_contains : root267.Contains (rootPhase 267) := by
  have hh := CBox.mul_contains mid267_contains root1_contains (c:=root267) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def root268 : CBox := ⟨⟨(-73564563599667423534212265940),(-73564563599667423527178539359)⟩,⟨997290456678690216132033310087,997290456678690216138979520779⟩⟩
lemma root268_contains : root268.Contains (rootPhase 268) := by
  have hh := CBox.mul_contains root134_contains root134_contains (c:=root268) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def mid269 : CBox := root268
lemma mid269_contains : mid269.Contains (rootPhase 268) := root268_contains
def root269 : CBox := ⟨⟨(-79682437971430121151902300879),(-79682437971430121144806586752)⟩,⟨996820299291165714969035360165,996820299291165714976026165500⟩⟩
lemma root269_contains : root269.Contains (rootPhase 269) := by
  have hh := CBox.mul_contains mid269_contains root1_contains (c:=root269) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def root270 : CBox := ⟨⟨(-85797312344439890466354554577),(-85797312344439890459233596943)⟩,⟨996312612182778012623609783240,996312612182778012630629398409⟩⟩
lemma root270_contains : root270.Contains (rootPhase 270) := by
  have hh := CBox.mul_contains root135_contains root135_contains (c:=root270) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def mid271 : CBox := root270
lemma mid271_contains : mid271.Contains (rootPhase 270) := root270_contains
def root271 : CBox := ⟨⟨(-91908956497132728629824315250),(-91908956497132728622640938829)⟩,⟨995767414467659793978848536795,995767414467659793985913519393⟩⟩
lemma root271_contains : root271.Contains (rootPhase 271) := by
  have hh := CBox.mul_contains mid271_contains root1_contains (c:=root271) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def root272 : CBox := ⟨⟨(-98017140329560601999039525950),(-98017140329560601991842602591)⟩,⟨995184726672196886241173636262,995184726672196886248254906132⟩⟩
lemma root272_contains : root272.Contains (rootPhase 272) := by
  have hh := CBox.mul_contains root136_contains root136_contains (c:=root272) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def mid273 : CBox := root272
lemma mid273_contains : mid273.Contains (rootPhase 272) := root272_contains
def root273 : CBox := ⟨⟨(-104121633872054579125823029710),(-104121633872054579118563331141)⟩,⟨994564570734255452115411771960,994564570734255452122539112870⟩⟩
lemma root273_contains : root273.Contains (rootPhase 273) := by
  have hh := CBox.mul_contains mid273_contains root1_contains (c:=root273) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def root274 : CBox := ⟨⟨(-110222207293883058812794310790),(-110222207293883058805510064508)⟩,⟨993906970002356041543206261483,993906970002356041550361422473⟩⟩
lemma root274_contains : root274.Contains (rootPhase 274) := by
  have hh := CBox.mul_contains root137_contains root137_contains (c:=root274) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def mid275 : CBox := root274
lemma mid275_contains : mid275.Contains (rootPhase 274) := root274_contains
def root275 : CBox := ⟨⟨(-116318630911904767257474785498),(-116318630911904767250127335646)⟩,⟨993211949234794533100852817244,993211949234794533108054822035⟩⟩
lemma root275_contains : root275.Contains (rootPhase 275) := by
  have hh := CBox.mul_contains mid275_contains root1_contains (c:=root275) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def root276 : CBox := ⟨⟨(-122410675199216198503646455203),(-122410675199216198496283254871)⟩,⟨992479534598709998153001724123,992479534598709998160221850846⟩⟩
lemma root276_contains : root276.Contains (rootPhase 276) := by
  have hh := CBox.mul_contains root138_contains root138_contains (c:=root276) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def mid277 : CBox := root276
lemma mid277_contains : mid277.Contains (rootPhase 276) := root276_contains
def root277 : CBox := ⟨⟨(-128498110793793172629392942841),(-128498110793793172621966168114)⟩,⟨991709753669099522856252299134,991709753669099522863519990891⟩⟩
lemma root277_contains : root277.Contains (rootPhase 277) := by
  have hh := CBox.mul_contains mid277_contains root1_contains (c:=root277) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def root278 : CBox := ⟨⟨(-134580708507126186321351195973),(-134580708507126186313900616294)⟩,⟨990902635427780025104417598155,990902635427780025111712107245⟩⟩
lemma root278_contains : root278.Contains (rootPhase 278) := by
  have hh := CBox.mul_contains root139_contains root139_contains (c:=root278) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def mid279 : CBox := root278
lemma mid279_contains : mid279.Contains (rootPhase 278) := root278_contains
def root279 : CBox := ⟨⟨(-140658239332849230719817108340),(-140658239332849230712302528743)⟩,⟨990058210262297105502054462178,990058210262297105509397308676⟩⟩
lemma root279_contains : root279.Contains (rootPhase 279) := by
  have hh := CBox.mul_contains mid279_contains root1_contains (c:=root279) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def root280 : CBox := ⟨⟨(-146730474455361751663887775155),(-146730474455361751656361267328)⟩,⟨989176509964780973447806406903,989176509964780973455162970428⟩⟩
lemma root280_contains : root280.Contains (rootPhase 280) := by
  have hh := CBox.mul_contains root140_contains root140_contains (c:=root280) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def mid281 : CBox := root280
lemma mid281_contains : mid281.Contains (rootPhase 280) := root280_contains
def root281 : CBox := ⟨⟨(-152797185258443427725409794795),(-152797185258443427717818939873)⟩,⟨988257567730749491400892168519,988257567730749491408297771379⟩⟩
lemma root281_contains : root281.Contains (rootPhase 281) := by
  have hh := CBox.mul_contains mid281_contains root1_contains (c:=root281) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def root282 : CBox := ⟨⟨(-158858143333861441689473362920),(-158858143333861441681859478885)⟩,⟨987301418157858382395893968678,987301418157858382403325363380⟩⟩
lemma root282_contains : root282.Contains (rootPhase 282) := by
  have hh := CBox.mul_contains root141_contains root141_contains (c:=root282) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def mid283 : CBox := root282
lemma mid283_contains : mid283.Contains (rootPhase 282) := root282_contains
def root283 : CBox := ⟨⟨(-164913120489969921423312750579),(-164913120489969921415634097005)⟩,⟨986308097244598647859342170350,986308097244598647866823375866⟩⟩
lemma root283_contains : root283.Contains (rootPhase 283) := by
  have hh := CBox.mul_contains mid283_contains root1_contains (c:=root283) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def root284 : CBox := ⟨⟨(-170961888760301226368775987327),(-170961888760301226361083731290)⟩,⟨985277642388941244770046879971,985277642388941244777543157932⟩⟩
lemma root284_contains : root284.Contains (rootPhase 284) := by
  have hh := CBox.mul_contains root142_contains root142_contains (c:=root284) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def mid285 : CBox := root284
lemma mid285_contains : mid285.Contains (rootPhase 284) := root284_contains
def root285 : CBox := ⟨⟨(-177004220412148756202009171615),(-177004220412148756194251787374)⟩,⟨984210092386929073189868860430,984210092386929073197415665135⟩⟩
lemma root285_contains : root285.Contains (rootPhase 285) := by
  have hh := CBox.mul_contains mid285_contains root1_contains (c:=root285) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def root286 : CBox := ⟨⟨(-183039887955140958521716084325),(-183039887955140958513936493517)⟩,⟨983105487431216327176274494683,983105487431216327183846051620⟩⟩
lemma root286_contains : root286.Contains (rootPhase 286) := by
  have hh := CBox.mul_contains root143_contains root143_contains (c:=root286) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def mid287 : CBox := root286
lemma mid287_contains : mid287.Contains (rootPhase 286) := root286_contains
def root287 : CBox := ⟨⟨(-189068664149806212760217132563),(-189068664149806212752371994170)⟩,⟨981963869109555264068787041859,981963869109555264076409895747⟩⟩
lemma root287_contains : root287.Contains (rootPhase 287) := by
  have hh := CBox.mul_contains mid287_contains root1_contains (c:=root287) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def root288 : CBox := ⟨⟨(-195090322016128267853511350304),(-195090322016128267845657751910)⟩,⟨980785280403230449122107640958,980785280403230449129739762163⟩⟩
lemma root288_contains : root288.Contains (rootPhase 288) := by
  have hh := CBox.mul_contains root144_contains root144_contains (c:=root288) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def mid289 : CBox := root288
lemma mid289_contains : mid289.Contains (rootPhase 288) := root288_contains
def root289 : CBox := ⟨⟨(-201104634842091911563705861114),(-201104634842091911555786388688)⟩,⟨979569765685440534435216626953,979569765685440534442900733262⟩⟩
lemma root289_contains : root289.Contains (rootPhase 289) := by
  have hh := CBox.mul_contains mid289_contains root1_contains (c:=root289) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def root290 : CBox := ⟨⟨(-207111376192218549713391847833),(-207111376192218549705451021763)⟩,⟨978317370719627633102109828785,978317370719627633109817624581⟩⟩
lemma root290_contains : root290.Contains (rootPhase 290) := by
  have hh := CBox.mul_contains root145_contains root145_contains (c:=root290) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def mid291 : CBox := root290
lemma mid291_contains : mid291.Contains (rootPhase 290) := root290_contains
def root291 : CBox := ⟨⟨(-213110319916091373973069266074),(-213110319916091373965062149949)⟩,⟨977028142657754351481700580951,977028142657754351489461130242⟩⟩
lemma root291_contains : root291.Contains (rootPhase 291) := by
  have hh := CBox.mul_contains mid291_contains root1_contains (c:=root291) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def root292 : CBox := ⟨⟨(-219101240156869797233057655352),(-219101240156869797225039247687)⟩,⟨975702130038528544456215164154,975702130038528544463987598304⟩⟩
lemma root292_contains : root292.Contains (rootPhase 292) := by
  have hh := CBox.mul_contains root146_contains root146_contains (c:=root292) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def mid293 : CBox := root292
lemma mid293_contains : mid293.Contains (rootPhase 292) := root292_contains
def root293 : CBox := ⟨⟨(-225083911359792835996998197683),(-225083911359792835988913154359)⟩,⟨974339382785575860514505261080,974339382785575860522331157508⟩⟩
lemma root293_contains : root293.Contains (rootPhase 293) := by
  have hh := CBox.mul_contains mid293_contains root1_contains (c:=root293) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def root294 : CBox := ⟨⟨(-231058108280671119648604911912),(-231058108280671119640499417291)⟩,⟨972939952205560145463483283007,972939952205560145471331792398⟩⟩
lemma root294_contains : root294.Contains (rootPhase 294) := by
  have hh := CBox.mul_contains root147_contains root147_contains (c:=root294) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def mid295 : CBox := root294
lemma mid295_contains : mid295.Contains (rootPhase 294) := root294_contains
def root295 : CBox := ⟨⟨(-237023605994367206873140859525),(-237023605994367206864968316520)⟩,⟨971503890986251775532826516216,971503890986251775540729254113⟩⟩
lemma root295_contains : root295.Contains (rootPhase 295) := by
  have hh := CBox.mul_contains mid295_contains root1_contains (c:=root295) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def root296 : CBox := ⟨⟨(-242980179903263889953684973615),(-242980179903263889945505626218)⟩,⟨970031253194543992599698533520,970031253194543992607608001290⟩⟩
lemma root296_contains : root296.Contains (rootPhase 296) := by
  have hh := CBox.mul_contains root148_contains root148_contains (c:=root296) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def mid297 : CBox := root296
lemma mid297_contains : mid297.Contains (rootPhase 296) := root296_contains
def root297 : CBox := ⟨⟨(-248927605745720168116129711558),(-248927605745720168107882998426)⟩,⟨968522094274417316216765953134,968522094274417316224730334020⟩⟩
lemma root297_contains : root297.Contains (rootPhase 297) := by
  have hh := CBox.mul_contains mid297_contains root1_contains (c:=root297) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def root298 : CBox := ⟨⟨(-254865659604514571559439769932),(-254865659604514571551173539145)⟩,⟨966976471044852109082877805545,966976471044852109090863700708⟩⟩
lemma root298_contains : root298.Contains (rootPhase 298) := by
  have hh := CBox.mul_contains root149_contains root149_contains (c:=root298) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def mid299 : CBox := root298
lemma mid299_contains : mid299.Contains (rootPhase 298) := root298_contains
def root299 : CBox := ⟨⟨(-260794117915275518285681660325),(-260794117915275518277347654640)⟩,⟨965394441697689374546464269950,965394441697689374554505841768⟩⟩
lemma root299_contains : root299.Contains (rootPhase 299) := by
  have hh := CBox.mul_contains mid299_contains root1_contains (c:=root299) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def root300 : CBox := ⟨⟨(-266712757474898386330788278784),(-266712757474898386322445464149)⟩,⟨963776065795439866682071122618,963776065795439866690121245383⟩⟩
lemma root300_contains : root300.Contains (rootPhase 300) := by
  have hh := CBox.mul_contains root150_contains root150_contains (c:=root300) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def mid301 : CBox := root300
lemma mid301_contains : mid301.Contains (rootPhase 300) := root300_contains
def root301 : CBox := ⟨⟨(-272621355449948984498885437039),(-272621355449948984490474515858)⟩,⟨962121404269041595425173484704,962121404269041595433279983927⟩⟩
lemma root301_contains : root301.Contains (rootPhase 301) := by
  have hh := CBox.mul_contains mid301_contains root1_contains (c:=root301) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def root302 : CBox := ⟨⟨(-278519689385053105213397830721),(-278519689385053105204968373992)⟩,⟨960430519415565811194584655296,960430519415565811202711555149⟩⟩
lemma root302_contains : root302.Contains (rootPhase 302) := by
  have hh := CBox.mul_contains root151_contains root151_contains (c:=root302) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def mid303 : CBox := root302
lemma mid303_contains : mid303.Contains (rootPhase 302) := root302_contains
def root303 : CBox := ⟨⟨(-284407537211271843623896187058),(-284407537211271843615398218163)⟩,⟨958703474895871555370157250763,958703474895871555378341287552⟩⟩
lemma root303_contains : root303.Contains (rootPhase 303) := by
  have hh := CBox.mul_contains mid303_contains root1_contains (c:=root303) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def root304 : CBox := ⟨⟨(-290284677254462367641781396485),(-290284677254462367633280420281)⟩,⟨956940335732208864931298829065,956940335732208864939484840905⟩⟩
lemma root304_contains : root304.Contains (rootPhase 304) := by
  have hh := CBox.mul_contains root152_contains root152_contains (c:=root304) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def mid305 : CBox := root304
lemma mid305_contains : mid305.Contains (rootPhase 304) := root304_contains
def root305 : CBox := ⟨⟨(-296150888243623824127411429977),(-296150888243623824118841646926)⟩,⟨955141168305770721493620184234,955141168305770721501864000193⟩⟩
lemma root305_contains : root305.Contains (rootPhase 305) := by
  have hh := CBox.mul_contains mid305_contains root1_contains (c:=root305) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def root306 : CBox := ⟨⟨(-302005949319228067009099107514),(-302005949319228067000511799119)⟩,⟨953306040354193836912183615668,953306040354193836920446696747⟩⟩
lemma root306_contains : root306.Contains (rootPhase 306) := by
  have hh := CBox.mul_contains root153_contains root153_contains (c:=root306) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def mid307 : CBox := root306
lemma mid307_contains : mid307.Contains (rootPhase 306) := root306_contains
def root307 : CBox := ⟨⟨(-307849640041534893687735868974),(-307849640041534893679079351967)⟩,⟨951435020969008369544579877165,951435020969008369552901519223⟩⟩
lemma root307_contains : root307.Contains (rootPhase 307) := by
  have hh := CBox.mul_contains mid307_contains root1_contains (c:=root307) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def root308 : CBox := ⟨⟨(-313681740398891476662155829196),(-313681740398891476653493143307)⟩,⟨949528180593036667191328162135,949528180593036667199654881561⟩⟩
lemma root308_contains : root308.Contains (rootPhase 308) := by
  have hh := CBox.mul_contains root154_contains root154_contains (c:=root308) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def mid309 : CBox := root308
lemma mid309_contains : mid309.Contains (rootPhase 308) := root308_contains
def root309 : CBox := ⟨⟨(-319502030816015677907231624392),(-319502030816015677898499413142)⟩,⟨947585591017741134648740065736,947585591017741134657126035130⟩⟩
lemma root309_contains : root309.Contains (rootPhase 309) := by
  have hh := CBox.mul_contains mid309_contains root1_contains (c:=root309) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def root310 : CBox := ⟨⟨(-325310292162262934141677830959),(-325310292162262934132929155936)⟩,⟨945607325380521325726279318966,945607325380521325734683402770⟩⟩
lemma root310_contains : root310.Contains (rootPhase 310) := by
  have hh := CBox.mul_contains root155_contains root155_contains (c:=root310) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def mid311 : CBox := root310
lemma mid311_contains : mid311.Contains (rootPhase 310) := root310_contains
def root311 : CBox := ⟨⟨(-331106305759876401742950290933),(-331106305759876401734131692579)⟩,⟨943593458161960361490595585604,943593458161960361499059672277⟩⟩
lemma root311_contains : root311.Contains (rootPhase 311) := by
  have hh := CBox.mul_contains mid311_contains root1_contains (c:=root311) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def root312 : CBox := ⟨⟨(-336889853392220050695014651767),(-336889853392220050686195081501)⟩,⟨941544065183020778407794164371,941544065183020778416257355510⟩⟩
lemma root312_contains : root312.Contains (rootPhase 312) := by
  have hh := CBox.mul_contains root156_contains root156_contains (c:=root312) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def mid313 : CBox := root312
lemma mid313_contains : mid313.Contains (rootPhase 312) := root312_contains
def root313 : CBox := ⟨⟨(-342660717311994397598579854707),(-342660717311994397589690077668)⟩,⟨939459223602189911957913815202,939459223602189911966437668864⟩⟩
lemma root313_contains : root313.Contains (rootPhase 313) := by
  have hh := CBox.mul_contains mid313_contains root1_contains (c:=root313) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def root314 : CBox := ⟨⟨(-348418680249434568425115405843),(-348418680249434568416210255447)⟩,⟨937339011912574923197125795708,937339011912574923205666592076⟩⟩
lemma root314_contains : root314.Contains (rootPhase 314) := by
  have hh := CBox.mul_contains root157_contains root157_contains (c:=root314) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def mid315 : CBox := root314
lemma mid315_contains : mid315.Contains (rootPhase 314) := root314_contains
def root315 : CBox := ⟨⟨(-354163525420490382363239103281),(-354163525420490382354263352224)⟩,⟨935183509938947577637393046998,935183509938947577645995254290⟩⟩
lemma root315_contains : root315.Contains (rootPhase 315) := by
  have hh := CBox.mul_contains mid315_contains root1_contains (c:=root315) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def root316 : CBox := ⟨⟨(-359895036534988148780950678734),(-359895036534988148771971564411)⟩,⟨932992798834738887706835132008,932992798834738887715438794686⟩⟩
lemma root316_contains : root316.Contains (rootPhase 316) := by
  have hh := CBox.mul_contains root158_contains root158_contains (c:=root316) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def mid317 : CBox := root316
lemma mid317_contains : mid317.Contains (rootPhase 316) := root316_contains
def root317 : CBox := ⟨⟨(-365612997804773870017628512036),(-365612997804773870008578496146)⟩,⟨930766961078983731940006176569,930766961078983731948671926530⟩⟩
lemma root317_contains : root317.Contains (rootPhase 317) := by
  have hh := CBox.mul_contains mid317_contains root1_contains (c:=root317) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def root318 : CBox := ⟨⟨(-371317193951837543417825661273),(-371317193951837543408761412703)⟩,⟨928506080473215565932283326493,928506080473215565940964831288⟩⟩
lemma root318_contains : root318.Contains (rootPhase 318) := by
  have hh := CBox.mul_contains root159_contains root159_contains (c:=root318) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def mid319 : CBox := root318
lemma mid319_contains : mid319.Contains (rootPhase 318) := root318_contains
def root319 : CBox := ⟨⟨(-377007410216418256732495065515),(-377007410216418256723359525546)⟩,⟨926210242138311341969867843277,926210242138311341978612178894⟩⟩
lemma root319_contains : root319.Contains (rootPhase 319) := by
  have hh := CBox.mul_contains mid319_contains root1_contains (c:=root319) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def root320 : CBox := ⟨⟨(-382683432365089771734386226768),(-382683432365089771725254345675)⟩,⟨923879532511286756123250801936,923879532511286756131988638187⟩⟩
lemma root320_contains : root320.Contains (rootPhase 320) := by
  have hh := CBox.mul_contains root160_contains root160_contains (c:=root320) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def mid321 : CBox := root320
lemma mid321_contains : mid321.Contains (rootPhase 320) := root320_contains
def root321 : CBox := ⟨⟨(-388345046698826291630956313895),(-388345046698826291621752885968)⟩,⟨921514039342041943460422088012,921514039342041943469223390530⟩⟩
lemma root321_contains : root321.Contains (rootPhase 321) := by
  have hh := CBox.mul_contains mid321_contains root1_contains (c:=root321) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def root322 : CBox := ⟨⟨(-393992040061048108602158651999),(-393992040061048108592942156100)⟩,⟨919113851690057743903486118831,919113851690057743912301968571⟩⟩
lemma root322_contains : root322.Contains (rootPhase 322) := by
  have hh := CBox.mul_contains root161_contains root161_contains (c:=root322) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def mid323 : CBox := root322
lemma mid323_contains : mid323.Contains (rootPhase 322) := root322_contains
def root323 : CBox := ⟨⟨(-399624199845646828550123598364),(-399624199845646828540835170204)⟩,⟨916679059921042663111423057411,916679059921042663120303111511⟩⟩
lemma root323_contains : root323.Contains (rootPhase 323) := by
  have hh := CBox.mul_contains mid323_contains root1_contains (c:=root323) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def root324 : CBox := ⟨⟨(-405241314004989870914488615014),(-405241314004989870905199776129)⟩,⟨914209755703530654629971812488,914209755703530654638849562989⟩⟩
lemma root324_contains : root324.Contains (rootPhase 324) := by
  have hh := CBox.mul_contains root162_contains root162_contains (c:=root324) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def mid325 : CBox := root324
lemma mid325_contains : mid325.Contains (rootPhase 324) := root324_contains
def root325 : CBox := ⟨⟨(-410843171057903942189510554939),(-410843171057903942180149499713)⟩,⟨911706032005429851399311633456,911706032005429851408254250238⟩⟩
lemma root325_contains : root325.Contains (rootPhase 325) := by
  have hh := CBox.mul_contains mid325_contains root1_contains (c:=root325) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def root326 : CBox := ⟨⟨(-416429560097637182568649103024),(-416429560097637182559276198955)⟩,⟨909167983090522376558782164946,909167983090522376567738104170⟩⟩
lemma root326_contains : root326.Contains (rootPhase 326) := by
  have hh := CBox.mul_contains root163_contains root163_contains (c:=root326) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def mid327 : CBox := root326
lemma mid327_contains : mid327.Contains (rootPhase 326) := root326_contains
def root327 : CBox := ⟨⟨(-422000270799799685947374745233),(-422000270799799685937929243721)⟩,⟨906595704514915365327814868617,906595704514915365336836406452⟩⟩
lemma root327_contains : root327.Contains (rootPhase 327) := by
  have hh := CBox.mul_contains mid327_contains root1_contains (c:=root327) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def root328 : CBox := ⟨⟨(-427555093430282094327051129601),(-427555093430282094317611165990)⟩,⟨903989293123443331581048830214,903989293123443331590061212415⟩⟩
lemma root328_contains : root328.Contains (rootPhase 328) := by
  have hh := CBox.mul_contains root164_contains root164_contains (c:=root328) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def mid329 : CBox := root328
lemma mid329_contains : mid329.Contains (rootPhase 328) := root328_contains
def root329 : CBox := ⟨⟨(-433093818853151968490343494831),(-433093818853151968480830688468)⟩,⟨901348847046022014565551161664,901348847046022014574629769627⟩⟩
lemma root329_contains : root329.Contains (rootPhase 329) := by
  have hh := CBox.mul_contains mid329_contains root1_contains (c:=root329) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def root330 : CBox := ⟨⟨(-438616238538527637653151982325),(-438616238538527637643628571941)⟩,⟨898674465693953843036765394819,898674465693953843045856081301⟩⟩
lemma root330_contains : root330.Contains (rootPhase 330) := by
  have hh := CBox.mul_contains root165_contains root165_contains (c:=root330) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def mid331 : CBox := root330
lemma mid331_contains : mid331.Contains (rootPhase 330) := root330_contains
def root331 : CBox := ⟨⟨(-444122144570429231648232282659),(-444122144570429231638635653054)⟩,⟨895966249756185155909305053513,895966249756185155918462691771⟩⟩
lemma root331_contains : root331.Contains (rootPhase 331) := by
  have hh := CBox.mul_contains mid331_contains root1_contains (c:=root331) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def root332 : CBox := ⟨⟨(-449611329654606600052456026756),(-449611329654606600042862099507)⟩,⟨893224301195515320337153897249,893224301195515320346305321531⟩⟩
lemma root332_contains : root332.Contains (rootPhase 332) := by
  have hh := CBox.mul_contains root166_contains root166_contains (c:=root332) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def mid333 : CBox := root332
lemma mid333_contains : mid333.Contains (rootPhase 332) := root332_contains
def root333 : CBox := ⟨⟨(-455083587126343823542067315050),(-455083587126343823532399902306)⟩,⟨890448723244757889946843757583,890448723244757889956062779340⟩⟩
lemma root333_contains : root333.Contains (rootPhase 333) := by
  have hh := CBox.mul_contains mid333_contains root1_contains (c:=root333) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def root334 : CBox := ⟨⟨(-460538710958240023639383967444),(-460538710958240023629707247623)⟩,⟨887639620402853947754858929104,887639620402853947764088767664⟩⟩
lemma root334_contains : root334.Contains (rootPhase 334) := by
  have hh := CBox.mul_contains root167_contains root167_contains (c:=root334) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def mid335 : CBox := root334
lemma mid335_contains : mid335.Contains (rootPhase 334) := root334_contains
def root335 : CBox := ⟨⟨(-465976495767966177908995176919),(-465976495767966177899244599736)⟩,⟨884797098430937780098639693204,884797098430937780107937848588⟩⟩
lemma root335_contains : root335.Contains (rootPhase 335) := by
  have hh := CBox.mul_contains mid335_contains root1_contains (c:=root335) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def root336 : CBox := ⟨⟨(-471396736825997648562621177112),(-471396736825997648552880971536)⟩,⟨881921264348355029707386471408,881921264348355029716669668982⟩⟩
lemma root336_contains : root336.Contains (rootPhase 336) := by
  have hh := CBox.mul_contains root168_contains root168_contains (c:=root336) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def mid337 : CBox := root336
lemma mid337_contains : mid337.Contains (rootPhase 336) := root336_contains
def root337 : CBox := ⟨⟨(-476799230063322133348428252275),(-476799230063322133338613973465)⟩,⟨879012226428633477825908314104,879012226428633477835260428484⟩⟩
lemma root337_contains : root337.Contains (rootPhase 337) := by
  have hh := CBox.mul_contains mid337_contains root1_contains (c:=root337) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def root338 : CBox := ⟨⟨(-482183772079122748523618079307),(-482183772079122748513795810799)⟩,⟨876070094195406607090413534515,876070094195406607099775186979⟩⟩
lemma root338_contains : root338.Contains (rootPhase 338) := by
  have hh := CBox.mul_contains root169_contains root169_contains (c:=root338) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def mid339 : CBox := root338
lemma mid339_contains : mid339.Contains (rootPhase 338) := root338_contains
def root339 : CBox := ⟨⟨(-487550160148435954647795236162),(-487550160148435954637898527517)⟩,⟨873094978418290098630609835720,873094978418290098640041117084⟩⟩
lemma root339_contains : root339.Contains (rootPhase 339) := by
  have hh := CBox.mul_contains mid339_contains root1_contains (c:=root339) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def root340 : CBox := ⟨⟨(-492898192229784036879333232308),(-492898192229784036869442477221)⟩,⟨870086991108711418646810787302,870086991108711418656231808651⟩⟩
lemma root340_contains : root340.Contains (rootPhase 340) := by
  have hh := CBox.mul_contains root170_contains root170_contains (c:=root340) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def mid341 : CBox := root340
lemma mid341_contains : mid341.Contains (rootPhase 340) := root340_contains
def root341 : CBox := ⟨⟨(-498227666972781852417326989102),(-498227666972781852407361546417)⟩,⟨867046245515692651474668254083,867046245515692651484159532046⟩⟩
lemma root341_contains : root341.Contains (rootPhase 341) := by
  have hh := CBox.mul_contains mid341_contains root1_contains (c:=root341) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def root342 : CBox := ⟨⟨(-503538383725717558698212651998),(-503538383725717558688240593407)⟩,⟨863972856121586737912604909582,863972856121586737922104427346⟩⟩
lemma root342_contains : root342.Contains (rootPhase 342) := by
  have hh := CBox.mul_contains root171_contains root171_contains (c:=root342) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def mid343 : CBox := root342
lemma mid343_contains : mid343.Contains (rootPhase 342) := root342_contains
def root343 : CBox := ⟨⟨(-508830142543107036938131503319),(-508830142543107036928084395116)⟩,⟨860866938637767279338995583056,860866938637767279348566061963⟩⟩
lemma root343_contains : root343.Contains (rootPhase 343) := by
  have hh := CBox.mul_contains mid343_contains root1_contains (c:=root343) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def root344 : CBox := ⟨⟨(-514102744193221726600068664072),(-514102744193221726590034250681)⟩,⟨857728610000272069896680027183,857728610000272069906232459280⟩⟩
lemma root344_contains : root344.Contains (rootPhase 344) := by
  have hh := CBox.mul_contains root172_contains root172_contains (c:=root344) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def mid345 : CBox := root344
lemma mid345_contains : mid345.Contains (rootPhase 344) := root344_contains
def root345 : CBox := ⟨⟨(-519355990165589587368241296824),(-519355990165589587358131630972)⟩,⟨854557988365400520762225839851,854557988365400520771849820336⟩⟩
lemma root345_contains : root345.Contains (rootPhase 345) := by
  have hh := CBox.mul_contains mid345_contains root1_contains (c:=root345) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def root346 : CBox := ⟨⟨(-524589682678468906221511271836),(-524589682678468906211396385643)⟩,⟨851355193105265142255639691569,851355193105265142265270597074⟩⟩
lemma root346_contains : root346.Contains (rootPhase 346) := by
  have hh := CBox.mul_contains root173_contains root173_contains (c:=root346) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def mid347 : CBox := root346
lemma mid347_contains : mid347.Contains (rootPhase 346) := root346_contains
def root347 : CBox := ⟨⟨(-529803624686294668222504036119),(-529803624686294668212313540663)⟩,⟨848120344803297251273436081987,848120344803297251283139232283⟩⟩
lemma root347_contains : root347.Contains (rootPhase 347) := by
  have hh := CBox.mul_contains mid347_contains root1_contains (c:=root347) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def root348 : CBox := ⟨⟨(-534997619887097210669520263576),(-534997619887097210659339122915)⟩,⟨844853565249707073253870197665,844853565249707073263558892015⟩⟩
lemma root348_contains : root348.Contains (rootPhase 348) := by
  have hh := CBox.mul_contains root174_contains root174_contains (c:=root348) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def mid349 : CBox := root348
lemma mid349_contains : mid349.Contains (rootPhase 348) := root348_contains
def root349 : CBox := ⟨⟨(-540171472729892881304325347437),(-540171472729892881294068369877)⟩,⟨841554977436898409597751316110,841554977436898409607512863241⟩⟩
lemma root349_contains : root349.Contains (rootPhase 349) := by
  have hh := CBox.mul_contains mid349_contains root1_contains (c:=root349) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def root350 : CBox := ⟨⟨(-545324988422046422320467609136),(-545324988422046422310206860915)⟩,⟨838224705554838043181235072160,838224705554838043191002209591⟩⟩
lemma root350_contains : root350.Contains (rootPhase 350) := by
  have hh := CBox.mul_contains root175_contains root175_contains (c:=root350) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def mid351 : CBox := root350
lemma mid351_contains : mid351.Contains (rootPhase 350) := root350_contains
def root351 : CBox := ⟨⟨(-550457972936604802983806676067),(-550457972936604802973469739328)⟩,⟨834862874986380056298592029994,834862874986380056308432708151⟩⟩
lemma root351_contains : root351.Contains (rootPhase 351) := by
  have hh := CBox.mul_contains mid351_contains root1_contains (c:=root351) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def root352 : CBox := ⟨⟨(-555570233019602224749336736176),(-555570233019602224739018213034)⟩,⟨831469612302545237072980603621,831469612302545237082796498323⟩⟩
lemma root352_contains : root352.Contains (rootPhase 352) := by
  have hh := CBox.mul_contains root176_contains root176_contains (c:=root352) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def mid353 : CBox := root352
lemma mid353_contains : mid353.Contains (rootPhase 352) := root352_contains
def root353 : CBox := ⟨⟨(-560661576197336023846252586734),(-560661576197336023835857707670)⟩,⟨828045045257755752061671945338,828045045257755752071561933684⟩⟩
lemma root353_contains : root353.Contains (rootPhase 353) := by
  have hh := CBox.mul_contains mid353_contains root1_contains (c:=root353) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def root354 : CBox := ⟨⟨(-565731810783613197396306709416),(-565731810783613197385909523649)⟩,⟨824589302785025264468935130770,824589302785025264478829362101⟩⟩
lemma root354_contains : root354.Contains (rootPhase 354) := by
  have hh := CBox.mul_contains root177_contains root177_contains (c:=root354) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def mid355 : CBox := root354
lemma mid355_contains : mid355.Contains (rootPhase 354) := root354_contains
def root355 : CBox := ⟨⟨(-570780745886967280239231011512),(-570780745886967280228757123774)⟩,⟨821102514991104679054513977652,821102514991104679064482981502⟩⟩
lemma root355_contains : root355.Contains (rootPhase 355) := by
  have hh := CBox.mul_contains mid355_contains root1_contains (c:=root355) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def root356 : CBox := ⟨⟨(-575808191417845300752542177932),(-575808191417845300742081168955)⟩,⟨817584813151583696499002569999,817584813151583696508952794025⟩⟩
lemma root356_contains : root356.Contains (rootPhase 356) := by
  have hh := CBox.mul_contains root178_contains root178_contains (c:=root356) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def mid357 : CBox := root356
lemma mid357_contains : mid357.Contains (rootPhase 356) := root356_contains
def root357 : CBox := ⟨⟨(-580813958095764545082201383111),(-580813958095764545071663465373)⟩,⟨814036329705948361648549823997,814036329705948361658575407104⟩⟩
lemma root357_contains : root357.Contains (rootPhase 357) := by
  have hh := CBox.mul_contains mid357_contains root1_contains (c:=root357) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def root358 : CBox := ⟨⟨(-585797857456438860334685190579),(-585797857456438860324146490377)⟩,⟨810457198252594791720724250282,810457198252594791730752705808⟩⟩
lemma root358_contains : root358.Contains (rootPhase 358) := by
  have hh := CBox.mul_contains root179_contains root179_contains (c:=root358) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def mid359 : CBox := root358
lemma mid359_contains : mid359.Contains (rootPhase 358) := root358_contains
def root359 : CBox := ⟨⟨(-590759701858874228430528651842),(-590759701858874228419912702312)⟩,⟨806847553543799272200486222749,806847553543799272210590706881⟩⟩
lemma root359_contains : root359.Contains (rootPhase 359) := by
  have hh := CBox.mul_contains mid359_contains root1_contains (c:=root359) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def root360 : CBox := ⟨⟨(-595699304492433343473664730924),(-595699304492433343463069230212)⟩,⟨803207531480644909800651295592,803207531480644909810728234323⟩⟩
lemma root360_contains : root360.Contains (rootPhase 360) := by
  have hh := CBox.mul_contains root180_contains root180_contains (c:=root360) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def mid361 : CBox := root360
lemma mid361_contains : mid361.Contains (rootPhase 360) := root360_contains
def root361 : CBox := ⟨⟨(-600616479383868926660540399513),(-600616479383868926649867493443)⟩,⟨799537269107905033494171821982,799537269107905033504325329481⟩⟩
lemma root361_contains : root361.Contains (rootPhase 361) := by
  have hh := CBox.mul_contains mid361_contains root1_contains (c:=root361) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def root362 : CBox := ⟨⟨(-605511041404325513927288581156),(-605511041404325513916616433927)⟩,⟨795836904608883536256705844673,795836904608883536266860841052⟩⟩
lemma root362_contains : root362.Contains (rootPhase 362) := by
  have hh := CBox.mul_contains root181_contains root181_contains (c:=root362) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def mid363 : CBox := root362
lemma mid363_contains : mid363.Contains (rootPhase 362) := root362_contains
def root363 : CBox := ⟨⟨(-610382806276309452723050092802),(-610382806276309452712300205467)⟩,⟨792106577300212351776207270560,792106577300212351786439495317⟩⟩
lemma root363_contains : root363.Contains (rootPhase 363) := by
  have hh := CBox.mul_contains mid363_contains root1_contains (c:=root363) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def root364 : CBox := ⟨⟨(-615231590580626845491600578910),(-615231590580626845480867236521)⟩,⟨788346427626606262003029795167,788346427626606262013238765375⟩⟩
lemma root364_contains : root364.Contains (rootPhase 364) := by
  have hh := CBox.mul_contains root182_contains root182_contains (c:=root364) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def mid365 : CBox := root364
lemma mid365_contains : mid365.Contains (rootPhase 364) := root364_contains
def root365 : CBox := ⟨⟨(-620057211763289178652991431771),(-620057211763289178642180164368)⟩,⟨784556597155575233017707833405,784556597155575233027994595448⟩⟩
lemma root365_contains : root365.Contains (rootPhase 365) := by
  have hh := CBox.mul_contains mid365_contains root1_contains (c:=root365) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def root366 : CBox := ⟨⟨(-624859488142386377090792056374),(-624859488142386377079983145381)⟩,⟨780737228572094478295392760988,780737228572094478305679605709⟩⟩
lemma root366_contains : root366.Contains (rootPhase 366) := by
  have hh := CBox.mul_contains root183_contains root183_contains (c:=root366) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def mid367 : CBox := root366
lemma mid367_contains : mid367.Contains (rootPhase 366) := root366_contains
def root367 : CBox := ⟨⟨(-629638238914927025379736800847),(-629638238914927025368849635883)⟩,⟨776888465673232450034582094934,776888465673232450044947380866⟩⟩
lemma root367_contains : root367.Contains (rootPhase 367) := by
  have hh := CBox.mul_contains mid367_contains root1_contains (c:=root367) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def root368 : CBox := ⟨⟨(-634393284163645498221910928749),(-634393284163645498211050069234)⟩,⟨773010453362736960804666989593,773010453362736960814997842652⟩⟩
lemma root368_contains : root368.Contains (rootPhase 368) := by
  have hh := CBox.mul_contains root184_contains root184_contains (c:=root368) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def mid369 : CBox := root368
lemma mid369_contains : mid369.Contains (rootPhase 368) := root368_contains
def root369 : CBox := ⟨⟨(-639124444863775743808263617958),(-639124444863775743797324385178)⟩,⟨769103337645579639340336024749,769103337645579639350745822247⟩⟩
lemma root369_contains : root369.Contains (rootPhase 369) := by
  have hh := CBox.mul_contains mid369_contains root1_contains (c:=root369) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def root370 : CBox := ⟨⟨(-643831542889791465074856344580),(-643831542889791465063921074840)⟩,⟨765167265622458925882515666424,765167265622458925892924132392⟩⟩
lemma root370_contains : root370.Contains (rootPhase 370) := by
  have hh := CBox.mul_contains root185_contains root185_contains (c:=root370) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def mid371 : CBox := root370
lemma mid371_contains : mid371.Contains (rootPhase 370) := root370_contains
def root371 : CBox := ⟨⟨(-648514401022112445091366932619),(-648514401022112445080352966837)⟩,⟨761202385484261814023358755150,761202385484261814033846804093⟩⟩
lemma root371_contains : root371.Contains (rootPhase 371) := by
  have hh := CBox.mul_contains mid371_contains root1_contains (c:=root371) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def root372 : CBox := ⟨⟨(-653172842953776764090995901566),(-653172842953776764080002257173)⟩,⟨757208846506484547569115941766,757208846506484547579576138598⟩⟩
lemma root372_contains : root372.Contains (rootPhase 372) := by
  have hh := CBox.mul_contains root186_contains root186_contains (c:=root372) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def mid373 : CBox := root372
lemma mid373_contains : mid373.Contains (rootPhase 372) := root372_contains
def root373 : CBox := ⟨⟨(-657806693297078656938011161805),(-657806693297078656926938659365)⟩,⟨753186799043612482477031354730,753186799043612482487571673258⟩⟩
lemma root373_contains : root373.Contains (rootPhase 373) := by
  have hh := CBox.mul_contains mid373_contains root1_contains (c:=root373) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def root374 : CBox := ⟨⟨(-662415777590171761119892394210),(-662415777590171761108825524077)⟩,⟨749136394523459325462794553978,749136394523459325473332099872⟩⟩
lemma root374_contains : root374.Contains (rootPhase 374) := by
  have hh := CBox.mul_contains root187_contains root187_contains (c:=root374) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def mid375 : CBox := root374
lemma mid375_contains : mid375.Contains (rootPhase 374) := root374_contains
def root375 : CBox := ⟨⟨(-666999922303637506657012795799),(-666999922303637506645866750944)⟩,⟨745057785441465962401447275313,745057785441465962412065570330⟩⟩
lemma root375_contains : root375.Contains (rootPhase 375) := by
  have hh := CBox.mul_contains mid375_contains root1_contains (c:=root375) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def root376 : CBox := ⟨⟨(-671558954847018400632217370466),(-671558954847018400621100080199)⟩,⟨740951125354959091169164721590,740951125354959091179745385829⟩⟩
lemma root376_contains : root376.Contains (rootPhase 376) := by
  have hh := CBox.mul_contains root188_contains root188_contains (c:=root376) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def mid377 : CBox := root376
lemma mid377_contains : mid377.Contains (rootPhase 376) := root376_contains
def root377 : CBox := ⟨⟨(-676092703575315960367295624630),(-676092703575315960356099054791)⟩,⟨736816568877369875083628772184,736816568877369875094290671719⟩⟩
lemma root377_contains : root377.Contains (rootPhase 377) := by
  have hh := CBox.mul_contains mid377_contains root1_contains (c:=root377) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def root378 : CBox := ⟨⟨(-680600997795453050601299355732),(-680600997795453050590110098987)⟩,⟨732654271672412834609034060129,732654271672412834619691737459⟩⟩
lemma root378_contains : root378.Contains (rootPhase 378) := by
  have hh := CBox.mul_contains root189_contains root189_contains (c:=root378) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def mid379 : CBox := root378
lemma mid379_contains : mid379.Contains (rootPhase 378) := root378_contains
def root379 : CBox := ⟨⟨(-685083667772700381368957295499),(-685083667772700381357688448956)⟩,⟨728464390448225196485470974530,728464390448225196496210502907⟩⟩
lemma root379_contains : root379.Contains (rootPhase 379) := by
  have hh := CBox.mul_contains mid379_contains root1_contains (c:=root379) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def root380 : CBox := ⟨⟨(-689540544737066924623619245623),(-689540544737066924612374624861)⟩,⟨724247082951466920934510133093,724247082951466920945217066226⟩⟩
lemma root380_contains : root380.Contains (rootPhase 380) := by
  have hh := CBox.mul_contains root190_contains root190_contains (c:=root380) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def mid381 : CBox := root380
lemma mid381_contains : mid381.Contains (rootPhase 380) := root380_contains
def root381 : CBox := ⟨⟨(-693971460889654009010658759934),(-693971460889654008999334411321)⟩,⟨720002507961381629070071766529,720002507961381629080861063095⟩⟩
lemma root381_contains : root381.Contains (rootPhase 381) := by
  have hh := CBox.mul_contains mid381_contains root1_contains (c:=root381) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def root382 : CBox := ⟨⟨(-698376249408972853561729152333),(-698376249408972853550413856242)⟩,⟨715730825283818654118913304923,715730825283818654129696903659⟩⟩
lemma root382_contains : root382.Contains (rootPhase 382) := by
  have hh := CBox.mul_contains root191_contains root191_contains (c:=root382) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def mid383 : CBox := root382
lemma mid383_contains : mid383.Contains (rootPhase 382) := root382_contains
def root383 : CBox := ⟨⟨(-702754744457225302459865803815),(-702754744457225302448470476069)⟩,⟨711432195745216441515458558249,711432195745216441526325124192⟩⟩
lemma root383_contains : root383.Contains (rootPhase 383) := by
  have hh := CBox.mul_contains mid383_contains root1_contains (c:=root383) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def root384 : CBox := ⟨⟨(-707106781186547524407773521426),(-707106781186547524396413902675)⟩,⟨707106781186547524394184557069,707106781186547524405005424275⟩⟩
lemma root384_contains : root384.Contains (rootPhase 384) := by
  have hh := CBox.mul_contains root192_contains root192_contains (c:=root384) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def mid385 : CBox := root384
lemma mid385_contains : mid385.Contains (rootPhase 384) := root384_contains
def root385 : CBox := ⟨⟨(-711432195745216441529095039118),(-711432195745216441517655328269)⟩,⟨702754744457225302446201996060,702754744457225302457106271223⟩⟩
lemma root385_contains : root385.Contains (rootPhase 385) := by
  have hh := CBox.mul_contains mid385_contains root1_contains (c:=root385) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def root386 : CBox := ⟨⟨(-715730825283818654132487433780),(-715730825283818654121058514832)⟩,⟨698376249408972853548093757062,698376249408972853558990858444⟩⟩
lemma root386_contains : root386.Contains (rootPhase 386) := by
  have hh := CBox.mul_contains root193_contains root193_contains (c:=root386) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def mid387 : CBox := root386
lemma mid387_contains : mid387.Contains (rootPhase 386) := root386_contains
def root387 : CBox := ⟨⟨(-720002507961381629083673373461),(-720002507961381629072164065448)⟩,⟨693971460889654008996961743824,693971460889654009007942844343⟩⟩
lemma root387_contains : root387.Contains (rootPhase 387) := by
  have hh := CBox.mul_contains mid387_contains root1_contains (c:=root387) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def root388 : CBox := ⟨⟨(-724247082951466920948040791153),(-724247082951466920936559702047)⟩,⟨689540544737066924609965817333,689540544737066924620909471630⟩⟩
lemma root388_contains : root388.Contains (rootPhase 388) := by
  have hh := CBox.mul_contains root194_contains root194_contains (c:=root388) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def mid389 : CBox := root388
lemma mid389_contains : mid389.Contains (rootPhase 388) := root388_contains
def root389 : CBox := ⟨⟨(-728464390448225196499042431853),(-728464390448225196487480840583)⟩,⟨685083667772700381355234609634,685083667772700381366262747580⟩⟩
lemma root389_contains : root389.Contains (rootPhase 389) := by
  have hh := CBox.mul_contains mid389_contains root1_contains (c:=root389) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def root390 : CBox := ⟨⟨(-732654271672412834622542451598),(-732654271672412834610993459819)⟩,⟨680600997795453050587606000287,680600997795453050598625455305⟩⟩
lemma root390_contains : root390.Contains (rootPhase 390) := by
  have hh := CBox.mul_contains root195_contains root195_contains (c:=root390) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def mid391 : CBox := root390
lemma mid391_contains : mid391.Contains (rootPhase 390) := root390_contains
def root391 : CBox := ⟨⟨(-736816568877369875097163739813),(-736816568877369875085533955649)⟩,⟨676092703575315960353541373171,676092703575315960364645890186⟩⟩
lemma root391_contains : root391.Contains (rootPhase 391) := by
  have hh := CBox.mul_contains mid391_contains root1_contains (c:=root391) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def root392 : CBox := ⟨⟨(-740951125354959091182624279279),(-740951125354959091171032037532)⟩,⟨671558954847018400618512275818,671558954847018400629568537901⟩⟩
lemma root392_contains : root392.Contains (rootPhase 392) := by
  have hh := CBox.mul_contains root196_contains root196_contains (c:=root392) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def mid393 : CBox := root392
lemma mid393_contains : mid393.Contains (rootPhase 392) := root392_contains
def root393 : CBox := ⟨⟨(-745057785441465962414949958854),(-745057785441465962403276875315)⟩,⟨666999922303637506643236068172,666999922303637506654377817899⟩⟩
lemma root393_contains : root393.Contains (rootPhase 393) := by
  have hh := CBox.mul_contains mid393_contains root1_contains (c:=root393) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def root394 : CBox := ⟨⟨(-749136394523459325476233457700),(-749136394523459325464574786333)⟩,⟨662415777590171761106145938687,662415777590171761117277493459⟩⟩
lemma root394_contains : root394.Contains (rootPhase 394) := by
  have hh := CBox.mul_contains root197_contains root197_contains (c:=root394) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def mid395 : CBox := root394
lemma mid395_contains : mid395.Contains (rootPhase 394) := root394_contains
def root395 : CBox := ⟨⟨(-753186799043612482490495919923),(-753186799043612482478756123641)⟩,⟨657806693297078656924204550762,657806693297078656935422158135⟩⟩
lemma root395_contains : root395.Contains (rootPhase 395) := by
  have hh := CBox.mul_contains mid395_contains root1_contains (c:=root395) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def root396 : CBox := ⟨⟨(-757208846506484547582507905772),(-757208846506484547570800440526)⟩,⟨653172842953776764077235728155,653172842953776764088410892590⟩⟩
lemma root396_contains : root396.Contains (rootPhase 396) := by
  have hh := CBox.mul_contains root198_contains root198_contains (c:=root396) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def mid397 : CBox := root396
lemma mid397_contains : mid397.Contains (rootPhase 396) := root396_contains
def root397 : CBox := ⟨⟨(-761202385484261814036788789493),(-761202385484261814025000112245)⟩,⟨648514401022112445077539232533,648514401022112445088800904693⟩⟩
lemma root397_contains : root397.Contains (rootPhase 397) := by
  have hh := CBox.mul_contains mid397_contains root1_contains (c:=root397) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def root398 : CBox := ⟨⟨(-765167265622458925895881218203),(-765167265622458925884108827107)⟩,⟨643831542889791465061059850256,643831542889791465072309785244⟩⟩
lemma root398_contains : root398.Contains (rootPhase 398) := by
  have hh := CBox.mul_contains root199_contains root199_contains (c:=root398) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def mid399 : CBox := root398
lemma mid399_contains : mid399.Contains (rootPhase 398) := root398_contains
def root399 : CBox := ⟨⟨(-769103337645579639353726352658),(-769103337645579639341872473513)⟩,⟨639124444863775743794407703566,639124444863775743805744697560⟩⟩
lemma root399_contains : root399.Contains (rootPhase 399) := by
  have hh := CBox.mul_contains mid399_contains root1_contains (c:=root399) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def root400 : CBox := ⟨⟨(-773010453362736960817978941942),(-773010453362736960806169432097)⟩,⟨634393284163645498208108498506,634393284163645498219389284029⟩⟩
lemma root400_contains : root400.Contains (rootPhase 400) := by
  have hh := CBox.mul_contains root200_contains root200_contains (c:=root400) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def mid401 : CBox := root400
lemma mid401_contains : mid401.Contains (rootPhase 400) := root400_contains
def root401 : CBox := ⟨⟨(-776888465673232450047935207235),(-776888465673232450036044204169)⟩,⟨629638238914927025365863794896,629638238914927025377232018647⟩⟩
lemma root401_contains : root401.Contains (rootPhase 401) := by
  have hh := CBox.mul_contains mid401_contains root1_contains (c:=root401) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def root402 : CBox := ⟨⟨(-780737228572094478308680689016),(-780737228572094478296807839563)⟩,⟨624859488142386377076951213543,624859488142386377088306163992⟩⟩
lemma root402_contains : root402.Contains (rootPhase 402) := by
  have hh := CBox.mul_contains root201_contains root201_contains (c:=root402) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def mid403 : CBox := root402
lemma mid403_contains : mid403.Contains (rootPhase 402) := root402_contains
def root403 : CBox := ⟨⟨(-784556597155575233031019630993),(-784556597155575233019065019751)⟩,⟨620057211763289178639091926475,620057211763289178650534852159⟩⟩
lemma root403_contains : root403.Contains (rootPhase 403) := by
  have hh := CBox.mul_contains mid403_contains root1_contains (c:=root403) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def root404 : CBox := ⟨⟨(-788346427626606262016267385631),(-788346427626606262004349291823)⟩,⟨615231590580626845477750413721,615231590580626845489145799677⟩⟩
lemma root404_contains : root404.Contains (rootPhase 404) := by
  have hh := CBox.mul_contains root202_contains root202_contains (c:=root404) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def mid405 : CBox := root404
lemma mid405_contains : mid405.Contains (rootPhase 404) := root404_contains
def root405 : CBox := ⟨⟨(-792106577300212351789480264898),(-792106577300212351777480349206)⟩,⟨610382806276309452709134167994,610382806276309452720617953487⟩⟩
lemma root405_contains : root405.Contains (rootPhase 405) := by
  have hh := CBox.mul_contains mid405_contains root1_contains (c:=root405) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def root406 : CBox := ⟨⟨(-795836904608883536269912963416),(-795836904608883536257933139435)⟩,⟨605511041404325513913405768135,605511041404325513924874706175⟩⟩
lemma root406_contains : root406.Contains (rootPhase 406) := by
  have hh := CBox.mul_contains root203_contains root203_contains (c:=root406) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def mid407 : CBox := root406
lemma mid407_contains : mid407.Contains (rootPhase 406) := root406_contains
def root407 : CBox := ⟨⟨(-799537269107905033507401941697),(-799537269107905033495340034673)⟩,⟨600616479383868926646599669940,600616479383868926658157530018⟩⟩
lemma root407_contains : root407.Contains (rootPhase 407) := by
  have hh := CBox.mul_contains mid407_contains root1_contains (c:=root407) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def root408 : CBox := ⟨⟨(-803207531480644909813802376575),(-803207531480644909801787226207)⟩,⟨595699304492433343459779425697,595699304492433343471277902961⟩⟩
lemma root408_contains : root408.Contains (rootPhase 408) := by
  have hh := CBox.mul_contains root204_contains root204_contains (c:=root408) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def mid409 : CBox := root408
lemma mid409_contains : mid409.Contains (rootPhase 408) := root408_contains
def root409 : CBox := ⟨⟨(-806847553543799272213674657582),(-806847553543799272201577434372)⟩,⟨590759701858874228416575618828,590759701858874228428163377095⟩⟩
lemma root409_contains : root409.Contains (rootPhase 409) := by
  have hh := CBox.mul_contains mid409_contains root1_contains (c:=root409) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def root410 : CBox := ⟨⟨(-810457198252594791733846123165),(-810457198252594791721770927513)⟩,⟨585797857456438860320766235573,585797857456438860332337576091⟩⟩
lemma root410_contains : root410.Contains (rootPhase 410) := by
  have hh := CBox.mul_contains root205_contains root205_contains (c:=root410) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def mid411 : CBox := root410
lemma mid411_contains : mid411.Contains (rootPhase 410) := root410_contains
def root411 : CBox := ⟨⟨(-814036329705948361661693811984),(-814036329705948361649536290093)⟩,⟨580813958095764545068225277407,580813958095764545079886406374⟩⟩
lemma root411_contains : root411.Contains (rootPhase 411) := by
  have hh := CBox.mul_contains mid411_contains root1_contains (c:=root411) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def root412 : CBox := ⟨⟨(-817584813151583696512070787505),(-817584813151583696499954069335)⟩,⟨575808191417845300738618372911,575808191417845300750226730467⟩⟩
lemma root412_contains : root412.Contains (rootPhase 412) := by
  have hh := CBox.mul_contains root206_contains root206_contains (c:=root412) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def mid413 : CBox := root412
lemma mid413_contains : mid413.Contains (rootPhase 412) := root412_contains
def root413 : CBox := ⟨⟨(-821102514991104679067614998531),(-821102514991104679055415922065)⟩,⟨570780745886967280225243246223,570780745886967280236941784299⟩⟩
lemma root413_contains : root413.Contains (rootPhase 413) := by
  have hh := CBox.mul_contains mid413_contains root1_contains (c:=root413) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def root414 : CBox := ⟨⟨(-824589302785025264481968909912),(-824589302785025264469793861150)⟩,⟨565731810783613197382353985315,565731810783613197394034500216⟩⟩
lemma root414_contains : root414.Contains (rootPhase 414) := by
  have hh := CBox.mul_contains root207_contains root207_contains (c:=root414) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def mid415 : CBox := root414
lemma mid415_contains : mid415.Contains (rootPhase 414) := root414_contains
def root415 : CBox := ⟨⟨(-828045045257755752074726988068),(-828045045257755752062469335363)⟩,⟨560661576197336023832243467984,560661576197336023844014655530⟩⟩
lemma root415_contains : root415.Contains (rootPhase 415) := by
  have hh := CBox.mul_contains mid415_contains root1_contains (c:=root415) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def root416 : CBox := ⟨⟨(-831469612302545237085953274163),(-831469612302545237073750289244)⟩,⟨555570233019602224735387948263,555570233019602224747090627042⟩⟩
lemma root416_contains : root416.Contains (rootPhase 416) := by
  have hh := CBox.mul_contains root208_contains root208_contains (c:=root416) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def mid417 : CBox := root416
lemma mid417_contains : mid417.Contains (rootPhase 416) := root416_contains
def root417 : CBox := ⟨⟨(-834862874986380056311600297735),(-834862874986380056299314771088)⟩,⟨550457972936604802969791202093,550457972936604802981584857648⟩⟩
lemma root417_contains : root417.Contains (rootPhase 417) := by
  have hh := CBox.mul_contains mid417_contains root1_contains (c:=root417) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def root418 : CBox := ⟨⟨(-838224705554838043194175426181),(-838224705554838043181915908981)⟩,⟨545324988422046422306488155266,545324988422046422318262199497⟩⟩
lemma root418_contains : root418.Contains (rootPhase 418) := by
  have hh := CBox.mul_contains root209_contains root209_contains (c:=root418) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def mid419 : CBox := root418
lemma mid419_contains : mid419.Contains (rootPhase 418) := root418_contains
def root419 : CBox := ⟨⟨(-841554977436898409610712053403),(-841554977436898409598369756986)⟩,⟨540171472729892881290290284108,540171472729892881302155781325⟩⟩
lemma root419_contains : root419.Contains (rootPhase 419) := by
  have hh := CBox.mul_contains mid419_contains root1_contains (c:=root419) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def root420 : CBox := ⟨⟨(-844853565249707073266753656369),(-844853565249707073254456498237)⟩,⟨534997619887097210655540503274,534997619887097210667347918668⟩⟩
lemma root420_contains : root420.Contains (rootPhase 420) := by
  have hh := CBox.mul_contains root210_contains root210_contains (c:=root420) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def mid421 : CBox := root420
lemma mid421_contains : mid421.Contains (rootPhase 420) := root420_contains
def root421 : CBox := ⟨⟨(-848120344803297251286349805589),(-848120344803297251273969865144)⟩,⟨529803624686294668208462148731,529803624686294668220361375643⟩⟩
lemma root421_contains : root421.Contains (rootPhase 421) := by
  have hh := CBox.mul_contains mid421_contains root1_contains (c:=root421) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def root422 : CBox := ⟨⟨(-851355193105265142268484833556),(-851355193105265142256132962113)⟩,⟨524589682678468906207506381287,524589682678468906219384361596⟩⟩
lemma root422_contains : root422.Contains (rootPhase 422) := by
  have hh := CBox.mul_contains root211_contains root211_contains (c:=root422) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def mid423 : CBox := root422
lemma mid423_contains : mid423.Contains (rootPhase 422) := root422_contains
def root423 : CBox := ⟨⟨(-854557988365400520775090530672),(-854557988365400520762655647517)⟩,⟨519355990165589587354181562817,519355990165589587366151814733⟩⟩
lemma root423_contains : root423.Contains (rootPhase 423) := by
  have hh := CBox.mul_contains mid423_contains root1_contains (c:=root423) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def root424 : CBox := ⟨⟨(-857728610000272069909462225726),(-857728610000272069897083651533)⟩,⟨514102744193221726586070822489,514102744193221726597970133754⟩⟩
lemma root424_contains : root424.Contains (rootPhase 424) := by
  have hh := CBox.mul_contains root212_contains root212_contains (c:=root424) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def mid425 : CBox := root424
lemma mid425_contains : mid425.Contains (rootPhase 424) := root424_contains
def root425 : CBox := ⟨⟨(-860866938637767279351809641994),(-860866938637767279339348129816)⟩,⟨508830142543107036924069945196,508830142543107036936061814698⟩⟩
lemma root425_contains : root425.Contains (rootPhase 425) := by
  have hh := CBox.mul_contains mid425_contains root1_contains (c:=root425) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def root426 : CBox := ⟨⟨(-863972856121586737925349729243),(-863972856121586737912918335070)⟩,⟨503538383725717558684189078224,503538383725717558696158077672⟩⟩
lemma root426_contains : root426.Contains (rootPhase 426) := by
  have hh := CBox.mul_contains root213_contains root213_contains (c:=root426) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def mid427 : CBox := root426
lemma mid427_contains : mid427.Contains (rootPhase 426) := root426_contains
def root427 : CBox := ⟨⟨(-867046245515692651487431766623),(-867046245515692651474917213500)⟩,⟨498227666972781852403249361905,498227666972781852415311363029⟩⟩
lemma root427_contains : root427.Contains (rootPhase 427) := by
  have hh := CBox.mul_contains mid427_contains root1_contains (c:=root427) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def root428 : CBox := ⟨⟨(-870086991108711418659495557655),(-870086991108711418647030566325)⟩,⟨492898192229784036865313966298,492898192229784036877312442280⟩⟩
lemma root428_contains : root428.Contains (rootPhase 428) := by
  have hh := CBox.mul_contains root214_contains root214_contains (c:=root428) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def mid429 : CBox := root428
lemma mid429_contains : mid429.Contains (rootPhase 428) := root428_contains
def root429 : CBox := ⟨⟨(-873094978418290098643322403545),(-873094978418290098630774280170)⟩,⟨487550160148435954633715701267,487550160148435954645807502618⟩⟩
lemma root429_contains : root429.Contains (rootPhase 429) := by
  have hh := CBox.mul_contains mid429_contains root1_contains (c:=root429) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def root430 : CBox := ⟨⟨(-876070094195406607103056207111),(-876070094195406607090540318448)⟩,⟨482183772079122748509577518450,482183772079122748521644785338⟩⟩
lemma root430_contains : root430.Contains (rootPhase 430) := by
  have hh := CBox.mul_contains root215_contains root215_contains (c:=root430) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def mid431 : CBox := root430
lemma mid431_contains : mid431.Contains (rootPhase 430) := root430_contains
def root431 : CBox := ⟨⟨(-879012226428633477838568862370),(-879012226428633477825969629133)⟩,⟨476799230063322133334334413608,476799230063322133346495432401⟩⟩
lemma root431_contains : root431.Contains (rootPhase 431) := by
  have hh := CBox.mul_contains mid431_contains root1_contains (c:=root431) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def root432 : CBox := ⟨⟨(-881921264348355029719961465370),(-881921264348355029707426241918)⟩,⟨471396736825997648548594031522,471396736825997648560675177883⟩⟩
lemma root432_contains : root432.Contains (rootPhase 432) := by
  have hh := CBox.mul_contains root216_contains root216_contains (c:=root432) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def mid433 : CBox := root432
lemma mid433_contains : mid433.Contains (rootPhase 432) := root432_contains
def root433 : CBox := ⟨⟨(-884797098430937780111244622005),(-884797098430937780098626179222)⟩,⟨465976495767966177894905691480,465976495767966177907080821062⟩⟩
lemma root433_contains : root433.Contains (rootPhase 433) := by
  have hh := CBox.mul_contains mid433_contains root1_contains (c:=root433) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def root434 : CBox := ⟨⟨(-887639620402853947767393321463),(-887639620402853947754809203298)⟩,⟨460538710958240023625334452342,460538710958240023637483409195⟩⟩
lemma root434_contains : root434.Contains (rootPhase 434) := by
  have hh := CBox.mul_contains root217_contains root217_contains (c:=root434) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def mid435 : CBox := root434
lemma mid435_contains : mid435.Contains (rootPhase 434) := root434_contains
def root435 : CBox := ⟨⟨(-890448723244757889959395176068),(-890448723244757889946727634861)⟩,⟨455083587126343823527965330725,455083587126343823540208679873⟩⟩
lemma root435_contains : root435.Contains (rootPhase 435) := by
  have hh := CBox.mul_contains mid435_contains root1_contains (c:=root435) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def root436 : CBox := ⟨⟨(-893224301195515320349625171400),(-893224301195515320337011646314)⟩,⟨449611329654606600038415494626,449611329654606600050589808591⟩⟩
lemma root436_contains : root436.Contains (rootPhase 436) := by
  have hh := CBox.mul_contains root218_contains root218_contains (c:=root436) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def mid437 : CBox := root436
lemma mid437_contains : mid437.Contains (rootPhase 436) := root436_contains
def root437 : CBox := ⟨⟨(-895966249756185155921801719924),(-895966249756185155909104829581)⟩,⟨444122144570429231634133370059,444122144570429231646402363995⟩⟩
lemma root437_contains : root437.Contains (rootPhase 437) := by
  have hh := CBox.mul_contains mid437_contains root1_contains (c:=root437) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def root438 : CBox := ⟨⟨(-898674465693953843049190881101),(-898674465693953843036530486352)⟩,⟨438616238538527637639094041583,438616238538527637651335170816⟩⟩
lemma root438_contains : root438.Contains (rootPhase 438) := by
  have hh := CBox.mul_contains root219_contains root219_contains (c:=root438) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def mid439 : CBox := root438
lemma mid439_contains : mid439.Contains (rootPhase 438) := root438_contains
def root439 : CBox := ⟨⟨(-901348847046022014577992873981),(-901348847046022014565248919046)⟩,⟨433093818853151968476233869869,433093818853151968488570070481⟩⟩
lemma root439_contains : root439.Contains (rootPhase 439) := by
  have hh := CBox.mul_contains mid439_contains root1_contains (c:=root439) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def root440 : CBox := ⟨⟨(-903989293123443331593404791727),(-903989293123443331580726967798)⟩,⟨427555093430282094313010032619,427555093430282094325263358773⟩⟩
lemma root440_contains : root440.Contains (rootPhase 440) := by
  have hh := CBox.mul_contains root220_contains root220_contains (c:=root440) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def mid441 : CBox := root440
lemma mid441_contains : mid441.Contains (rootPhase 440) := root440_contains
def root441 : CBox := ⟨⟨(-906595704514915365340197488256),(-906595704514915365327436245098)⟩,⟨422000270799799685933274028691,422000270799799685945622635363⟩⟩
lemma root441_contains : root441.Contains (rootPhase 441) := by
  have hh := CBox.mul_contains mid441_contains root1_contains (c:=root441) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def root442 : CBox := ⟨⟨(-909167983090522376571092976472),(-909167983090522376558370380034)⟩,⟨416429560097637182554590363252,416429560097637182566909434355⟩⟩
lemma root442_contains : root442.Contains (rootPhase 442) := by
  have hh := CBox.mul_contains root221_contains root221_contains (c:=root442) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def mid443 : CBox := root442
lemma mid443_contains : mid443.Contains (rootPhase 442) := root442_contains
def root443 : CBox := ⟨⟨(-911706032005429851411637845434),(-911706032005429851398831643950)⟩,⟨410843171057903942175400943935,410843171057903942187815668794⟩⟩
lemma root443_contains : root443.Contains (rootPhase 443) := by
  have hh := CBox.mul_contains mid443_contains root1_contains (c:=root443) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def root444 : CBox := ⟨⟨(-914209755703530654642216527205),(-914209755703530654629468862943)⟩,⟨405241314004989870900443596142,405241314004989870912783658122⟩⟩
lemma root444_contains : root444.Contains (rootPhase 444) := by
  have hh := CBox.mul_contains root222_contains root222_contains (c:=root444) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def mid445 : CBox := root444
lemma mid445_contains : mid445.Contains (rootPhase 444) := root444_contains
def root445 : CBox := ⟨⟨(-916679059921042663123690832195),(-916679059921042663110859652549)⟩,⟨399624199845646828536022106881,399624199845646828548458073108⟩⟩
lemma root445_contains : root445.Contains (rootPhase 445) := by
  have hh := CBox.mul_contains mid445_contains root1_contains (c:=root445) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def root446 : CBox := ⟨⟨(-919113851690057743915681454131),(-919113851690057743902891143909)⟩,⟨393992040061048108588100149837,393992040061048108600504861904⟩⟩
lemma root446_contains : root446.Contains (rootPhase 446) := by
  have hh := CBox.mul_contains root223_contains root223_contains (c:=root446) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def mid447 : CBox := root446
lemma mid447_contains : mid447.Contains (rootPhase 446) := root446_contains
def root447 : CBox := ⟨⟨(-921514039342041943472632040724),(-921514039342041943459758038433)⟩,⟨388345046698826291616847734573,388345046698826291629348705715⟩⟩
lemma root447_contains : root447.Contains (rootPhase 447) := by
  have hh := CBox.mul_contains mid447_contains root1_contains (c:=root447) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def root448 : CBox := ⟨⟨(-923879532511286756135371430705),(-923879532511286756122572596632)⟩,⟨382683432365089771720351675698,382683432365089771732759419097⟩⟩
lemma root448_contains : root448.Contains (rootPhase 448) := by
  have hh := CBox.mul_contains root224_contains root224_contains (c:=root448) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def mid449 : CBox := root448
lemma mid449_contains : mid449.Contains (rootPhase 448) := root448_contains
def root449 : CBox := ⟨⟨(-926210242138311341982013409211),(-926210242138311341969131085005)⟩,⟨377007410216418256718402247394,377007410216418256730906393774⟩⟩
lemma root449_contains : root449.Contains (rootPhase 449) := by
  have hh := CBox.mul_contains mid449_contains root1_contains (c:=root449) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def root450 : CBox := ⟨⟨(-928506080473215565944355844725),(-928506080473215565931516569601)⟩,⟨371317193951837543403776841129,371317193951837543416248057229⟩⟩
lemma root450_contains : root450.Contains (rootPhase 450) := by
  have hh := CBox.mul_contains root225_contains root225_contains (c:=root450) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def mid451 : CBox := root450
lemma mid451_contains : mid451.Contains (rootPhase 450) := root450_contains
def root451 : CBox := ⟨⟨(-930766961078983731952092488891),(-930766961078983731939169556454)⟩,⟨365612997804773870003530449471,365612997804773870016098404434⟩⟩
lemma root451_contains : root451.Contains (rootPhase 451) := by
  have hh := CBox.mul_contains mid451_contains root1_contains (c:=root451) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def root452 : CBox := ⟨⟨(-932992798834738887718838666696),(-932992798834738887705978790662)⟩,⟨359895036534988148766920364554,359895036534988148779407993313⟩⟩
lemma root452_contains : root452.Contains (rootPhase 452) := by
  have hh := CBox.mul_contains root226_contains root226_contains (c:=root452) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def mid453 : CBox := root452
lemma mid453_contains : mid453.Contains (rootPhase 452) := root452_contains
def root453 : CBox := ⟨⟨(-935183509938947577649417367818),(-935183509938947577636473956783)⟩,⟨354163525420490382349154253786,354163525420490382361738833699⟩⟩
lemma root453_contains : root453.Contains (rootPhase 453) := by
  have hh := CBox.mul_contains mid453_contains root1_contains (c:=root453) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def root454 : CBox := ⟨⟨(-937339011912574923209076450137),(-937339011912574923196178359372)⟩,⟨348418680249434568411075576529,348418680249434568423625482844⟩⟩
lemma root454_contains : root454.Contains (rootPhase 454) := by
  have hh := CBox.mul_contains root227_contains root227_contains (c:=root454) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def mid455 : CBox := root454
lemma mid455_contains : mid455.Contains (rootPhase 454) := root454_contains
def root455 : CBox := ⟨⟨(-939459223602189911969877497482),(-939459223602189911956895714016)⟩,⟨342660717311994397584491585877,342660717311994397597138760098⟩⟩
lemma root455_contains : root455.Contains (rootPhase 455) := by
  have hh := CBox.mul_contains mid455_contains root1_contains (c:=root455) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def root456 : CBox := ⟨⟨(-941544065183020778419669064823),(-941544065183020778406763397018)⟩,⟨336889853392220050681001660117,336889853392220050693553752243⟩⟩
lemma root456_contains : root456.Contains (rootPhase 456) := by
  have hh := CBox.mul_contains root228_contains root228_contains (c:=root456) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def mid457 : CBox := root456
lemma mid457_contains : mid457.Contains (rootPhase 456) := root456_contains
def root457 : CBox := ⟨⟨(-943593458161960361502492236876),(-943593458161960361489503087853)⟩,⟨331106305759876401728881845739,331106305759876401741531332898⟩⟩
lemma root457_contains : root457.Contains (rootPhase 457) := by
  have hh := CBox.mul_contains mid457_contains root1_contains (c:=root457) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def root458 : CBox := ⟨⟨(-945607325380521325738101706548),(-945607325380521325725160118819)⟩,⟨325310292162262934127655423577,325310292162262934140268525550⟩⟩
lemma root458_contains : root458.Contains (rootPhase 458) := by
  have hh := CBox.mul_contains root229_contains root229_contains (c:=root458) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def mid459 : CBox := root458
lemma mid459_contains : mid459.Contains (rootPhase 458) := root458_contains
def root459 : CBox := ⟨⟨(-947585591017741134660574685790),(-947585591017741134647549468931)⟩,⟨319502030816015677893161612165,319502030816015677905872406323⟩⟩
lemma root459_contains : root459.Contains (rootPhase 459) := by
  have hh := CBox.mul_contains mid459_contains root1_contains (c:=root459) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def root460 : CBox := ⟨⟨(-949528180593036667203078773526),(-949528180593036667190121189231)⟩,⟨313681740398891476648156768180,313681740398891476660781456137⟩⟩
lemma root460_contains : root460.Contains (rootPhase 460) := by
  have hh := CBox.mul_contains root230_contains root230_contains (c:=root460) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def mid461 : CBox := root460
lemma mid461_contains : mid461.Contains (rootPhase 460) := root460_contains
def root461 : CBox := ⟨⟨(-951435020969008369556349077332),(-951435020969008369543308019856)⟩,⟨307849640041534893673684221544,307849640041534893686406774731⟩⟩
lemma root461_contains : root461.Contains (rootPhase 461) := by
  have hh := CBox.mul_contains mid461_contains root1_contains (c:=root461) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def root462 : CBox := ⟨⟨(-953306040354193836923877946107),(-953306040354193836910886766933)⟩,⟨302005949319228066995094528859,302005949319228067007778929791⟩⟩
lemma root462_contains : root462.Contains (rootPhase 462) := by
  have hh := CBox.mul_contains root231_contains root231_contains (c:=root462) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def mid463 : CBox := root462
lemma mid463_contains : mid463.Contains (rootPhase 462) := root462_contains
def root463 : CBox := ⟨⟨(-955141168305770721505325997477),(-955141168305770721492251207041)⟩,⟨296150888243623824113360057893,296150888243623824126142601375⟩⟩
lemma root463_contains : root463.Contains (rootPhase 463) := by
  have hh := CBox.mul_contains mid463_contains root1_contains (c:=root463) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def root464 : CBox := ⟨⟨(-956940335732208864942912738127),(-956940335732208864929922492606)⟩,⟨290284677254462367627810482787,290284677254462367640488200845⟩⟩
lemma root464_contains : root464.Contains (rootPhase 464) := by
  have hh := CBox.mul_contains root232_contains root232_contains (c:=root464) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def mid465 : CBox := root464
lemma mid465_contains : mid465.Contains (rootPhase 464) := root464_contains
def root465 : CBox := ⟨⟨(-958703474895871555381791074849),(-958703474895871555368717487642)⟩,⟨284407537211271843609871443361,284407537211271843622647367865⟩⟩
lemma root465_contains : root465.Contains (rootPhase 465) := by
  have hh := CBox.mul_contains mid465_contains root1_contains (c:=root465) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def root466 : CBox := ⟨⟨(-960430519415565811206143033250),(-960430519415565811193121589115)⟩,⟨278519689385053105199421173466,278519689385053105212157231481⟩⟩
lemma root466_contains : root466.Contains (rootPhase 466) := by
  have hh := CBox.mul_contains root233_contains root233_contains (c:=root466) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def mid467 : CBox := root466
lemma mid467_contains : mid467.Contains (rootPhase 466) := root466_contains
def root467 : CBox := ⟨⟨(-962121404269041595436742553964),(-962121404269041595423637640222)⟩,⟨272621355449948984484862840723,272621355449948984497697362193⟩⟩
lemma root467_contains : root467.Contains (rootPhase 467) := by
  have hh := CBox.mul_contains mid467_contains root1_contains (c:=root467) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def root468 : CBox := ⟨⟨(-963776065795439866693555029403),(-963776065795439866680522305254)⟩,⟨266712757474898386316839843041,266712757474898386329582455704⟩⟩
lemma root468_contains : root468.Contains (rootPhase 468) := by
  have hh := CBox.mul_contains root234_contains root234_contains (c:=root468) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def mid469 : CBox := root468
lemma mid469_contains : mid469.Contains (rootPhase 468) := root468_contains
def root469 : CBox := ⟨⟨(-965394441697689374557964625982),(-965394441697689374544848622519)⟩,⟨260794117915275518271682611984,260794117915275518284523821035⟩⟩
lemma root469_contains : root469.Contains (rootPhase 469) := by
  have hh := CBox.mul_contains mid469_contains root1_contains (c:=root469) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def root470 : CBox := ⟨⟨(-966976471044852109094302122379),(-966976471044852109081240621389)⟩,⟨254865659604514571545489846256,254865659604514571558289399996⟩⟩
lemma root470_contains : root470.Contains (rootPhase 470) := by
  have hh := CBox.mul_contains root235_contains root235_contains (c:=root470) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def mid471 : CBox := root470
lemma mid471_contains : mid471.Contains (rootPhase 470) := root470_contains
def root471 : CBox := ⟨⟨(-968522094274417316228200227816),(-968522094274417316215055329772)⟩,⟨248927605745720168102134668477,248927605745720168115033055108⟩⟩
lemma root471_contains : root471.Contains (rootPhase 471) := by
  have hh := CBox.mul_contains mid471_contains root1_contains (c:=root471) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def root472 : CBox := ⟨⟨(-970031253194543992611041239461),(-970031253194543992597982532462)⟩,⟨242980179903263889939772030169,242980179903263889952562917401⟩⟩
lemma root472_contains : root472.Contains (rootPhase 472) := by
  have hh := CBox.mul_contains root236_contains root236_contains (c:=root472) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def mid473 : CBox := root472
lemma mid473_contains : mid473.Contains (rootPhase 472) := root472_contains
def root473 : CBox := ⟨⟨(-971503890986251775544186364266),(-971503890986251775531044545207)⟩,⟨237023605994367206859176677366,237023605994367206872066438660⟩⟩
lemma root473_contains : root473.Contains (rootPhase 473) := by
  have hh := CBox.mul_contains mid473_contains root1_contains (c:=root473) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def root474 : CBox := ⟨⟨(-972939952205560145474766526117),(-972939952205560145461681527393)⟩,⟨231058108280671119634690879511,231058108280671119647537240428⟩⟩
lemma root474_contains : root474.Contains (rootPhase 474) := by
  have hh := CBox.mul_contains root237_contains root237_contains (c:=root474) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def mid475 : CBox := root474
lemma mid475_contains : mid475.Contains (rootPhase 474) := root474_contains
def root475 : CBox := ⟨⟨(-974339382785575860525797696117),(-974339382785575860512629478054)⟩,⟨225083911359792835983039900935,225083911359792835995985351485⟩⟩
lemma root475_contains : root475.Contains (rootPhase 475) := by
  have hh := CBox.mul_contains mid475_contains root1_contains (c:=root475) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def root476 : CBox := ⟨⟨(-975702130038528544467421338711),(-975702130038528544454329896915)⟩,⟨219101240156869797219176763567,219101240156869797232024408752⟩⟩
lemma root476_contains : root476.Contains (rootPhase 476) := by
  have hh := CBox.mul_contains root238_contains root238_contains (c:=root476) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def mid477 : CBox := root476
lemma mid477_contains : mid477.Contains (rootPhase 476) := root476_contains
def root477 : CBox := ⟨⟨(-977028142657754351492921139618),(-977028142657754351479746704029)⟩,⟨213110319916091373959139743537,213110319916091373972086570289⟩⟩
lemma root477_contains : root477.Contains (rootPhase 477) := by
  have hh := CBox.mul_contains mid477_contains root1_contains (c:=root477) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def root478 : CBox := ⟨⟨(-978317370719627633113253202397),(-978317370719627633100137986004)⟩,⟨207111376192218549699513519432,207111376192218549712415136464⟩⟩
lemma root478_contains : root478.Contains (rootPhase 478) := by
  have hh := CBox.mul_contains root239_contains root239_contains (c:=root478) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def mid479 : CBox := root478
lemma mid479_contains : mid479.Contains (rootPhase 478) := root478_contains
def root479 : CBox := ⟨⟨(-979569765685440534446368474830),(-979569765685440534433170167894)⟩,⟨201104634842091911549784095954,201104634842091911562785088965⟩⟩
lemma root479_contains : root479.Contains (rootPhase 479) := by
  have hh := CBox.mul_contains mid479_contains root1_contains (c:=root479) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def root480 : CBox := ⟨⟨(-980785280403230449133164314521),(-980785280403230449120061865055)⟩,⟨195090322016128267839677489684,195090322016128267852559957106⟩⟩
lemma root480_contains : root480.Contains (rootPhase 480) := by
  have hh := CBox.mul_contains root240_contains root240_contains (c:=root480) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def mid481 : CBox := root480
lemma mid481_contains : mid481.Contains (rootPhase 480) := root480_contains
def root481 : CBox := ⟨⟨(-981963869109555264079859172139),(-981963869109555264066673983987)⟩,⟨189068664149806212746333664844,189068664149806212759315476934⟩⟩
lemma root481_contains : root481.Contains (rootPhase 481) := by
  have hh := CBox.mul_contains mid481_contains root1_contains (c:=root481) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def root482 : CBox := ⟨⟨(-983105487431216327187268899309),(-983105487431216327174145257257)⟩,⟨183039887955140958507884828998,183039887955140958520819695620⟩⟩
lemma root482_contains : root482.Contains (rootPhase 482) := by
  have hh := CBox.mul_contains root241_contains root241_contains (c:=root482) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def mid483 : CBox := root482
lemma mid483_contains : mid483.Contains (rootPhase 482) := root482_contains
def root483 : CBox := ⟨⟨(-984210092386929073200870972765),(-984210092386929073187664506100)⟩,⟨177004220412148756188135357488,177004220412148756201169741602⟩⟩
lemma root483_contains : root483.Contains (rootPhase 483) := by
  have hh := CBox.mul_contains mid483_contains root1_contains (c:=root483) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def root484 : CBox := ⟨⟨(-985277642388941244780961723141),(-985277642388941244767836564003)⟩,⟨170961888760301226354982808335,170961888760301226367913505594⟩⟩
lemma root484_contains : root484.Contains (rootPhase 484) := by
  have hh := CBox.mul_contains root242_contains root242_contains (c:=root484) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def mid485 : CBox := root484
lemma mid485_contains : mid485.Contains (rootPhase 484) := root484_contains
def root485 : CBox := ⟨⟨(-986308097244598647870269384149),(-986308097244598647857061661757)⟩,⟨164913120489969921409472947630,164913120489969921422503212646⟩⟩
lemma root485_contains : root485.Contains (rootPhase 485) := by
  have hh := CBox.mul_contains mid485_contains root1_contains (c:=root485) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def root486 : CBox := ⟨⟨(-987301418157858382406742890026),(-987301418157858382393599148292)⟩,⟨158858143333861441675686821158,158858143333861441688668313163⟩⟩
lemma root486_contains : root486.Contains (rootPhase 486) := by
  have hh := CBox.mul_contains root243_contains root243_contains (c:=root486) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def mid487 : CBox := root486
lemma mid487_contains : mid487.Contains (rootPhase 486) := root486_contains
def root487 : CBox := ⟨⟨(-988257567730749491411748095249),(-988257567730749491398521715212)⟩,⟨152797185258443427711581529456,152797185258443427724662740259⟩⟩
lemma root487_contains : root487.Contains (rootPhase 487) := by
  have hh := CBox.mul_contains mid487_contains root1_contains (c:=root487) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def root488 : CBox := ⟨⟨(-989176509964780973458568259057),(-989176509964780973445438112482)⟩,⟨146730474455361751650148434576,146730474455361751663109648450⟩⟩
lemma root488_contains : root488.Contains (rootPhase 488) := by
  have hh := CBox.mul_contains root244_contains root244_contains (c:=root488) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def mid489 : CBox := root488
lemma mid489_contains : mid489.Contains (rootPhase 488) := root488_contains
def root489 : CBox := ⟨⟨(-990058210262297105512829136810),(-990058210262297105499616712857)⟩,⟨140658239332849230706030780814,140658239332849230719091665515⟩⟩
lemma root489_contains : root489.Contains (rootPhase 489) := by
  have hh := CBox.mul_contains mid489_contains root1_contains (c:=root489) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def root490 : CBox := ⟨⟨(-990902635427780025115113447055),(-990902635427780025101967384334)⟩,⟨134580708507126186307619156164,134580708507126186320629497493⟩⟩
lemma root490_contains : root490.Contains (rootPhase 490) := by
  have hh := CBox.mul_contains root245_contains root245_contains (c:=root490) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def mid491 : CBox := root490
lemma mid491_contains : mid491.Contains (rootPhase 490) := root490_contains
def root491 : CBox := ⟨⟨(-991709753669099522866954415706),(-991709753669099522853726011674)⟩,⟨128498110793793172615620053556,128498110793793172628730194601⟩⟩
lemma root491_contains : root491.Contains (rootPhase 491) := by
  have hh := CBox.mul_contains mid491_contains root1_contains (c:=root491) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def root492 : CBox := ⟨⟨(-992479534598709998163615617848),(-992479534598709998150473071652)⟩,⟨122410675199216198489957462745,122410675199216198502957944227⟩⟩
lemma root492_contains : root492.Contains (rootPhase 492) := by
  have hh := CBox.mul_contains root246_contains root246_contains (c:=root492) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def mid493 : CBox := root492
lemma mid493_contains : mid493.Contains (rootPhase 492) := root492_contains
def root493 : CBox := ⟨⟨(-993211949234794533111477143931),(-993211949234794533098252554482)⟩,⟨116318630911904767243741176392,116318630911904767256841465432⟩⟩
lemma root493_contains : root493.Contains (rootPhase 493) := by
  have hh := CBox.mul_contains mid493_contains root1_contains (c:=root493) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def root494 : CBox := ⟨⟨(-993906970002356041553751208858),(-993906970002356041540595447886)⟩,⟨110222207293883058799116041431,110222207293883058812163942611⟩⟩
lemma root494_contains : root494.Contains (rootPhase 494) := by
  have hh := CBox.mul_contains root247_contains root247_contains (c:=root494) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def mid495 : CBox := root494
lemma mid495_contains : mid495.Contains (rootPhase 494) := root494_contains
def root495 : CBox := ⟨⟨(-994564570734255452125962299438),(-994564570734255452112724442503)⟩,⟨104121633872054579112104753441,104121633872054579125252568681⟩⟩
lemma root495_contains : root495.Contains (rootPhase 495) := by
  have hh := CBox.mul_contains mid495_contains root1_contains (c:=root495) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def root496 : CBox := ⟨⟨(-995184726672196886251626960179),(-995184726672196886238494295930)⟩,⟨98017140329560601985415596300,98017140329560601998433110692⟩⟩
lemma root496_contains : root496.Contains (rootPhase 496) := by
  have hh := CBox.mul_contains root248_contains root248_contains (c:=root496) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def mid497 : CBox := root496
lemma mid497_contains : mid497.Contains (rootPhase 496) := root496_contains
def root497 : CBox := ⟨⟨(-995767414467659793989312968143),(-995767414467659793976098632294)⟩,⟨91908956497132728616155201918,91908956497132728629272512607⟩⟩
lemma root497_contains : root497.Contains (rootPhase 497) := by
  have hh := CBox.mul_contains mid497_contains root1_contains (c:=root497) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def root498 : CBox := ⟨⟨(-996312612182778012633994327664),(-996312612182778012620851204316)⟩,⟨85797312344439890452741796985,85797312344439890465804961919⟩⟩
lemma root498_contains : root498.Contains (rootPhase 498) := by
  have hh := CBox.mul_contains root249_contains root249_contains (c:=root498) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def mid499 : CBox := root498
lemma mid499_contains : mid499.Contains (rootPhase 498) := root498_contains
def root499 : CBox := ⟨⟨(-996820299291165714979424747726),(-996820299291165714966199911524)⟩,⟨79682437971430121138250431029,79682437971430121151413476029⟩⟩
lemma root499_contains : root499.Contains (rootPhase 499) := by
  have hh := CBox.mul_contains mid499_contains root1_contains (c:=root499) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def root500 : CBox := ⟨⟨(-997290456678690216142333614450),(-997290456678690216129199112056)⟩,⟨73564563599667423520647528734,73564563599667423533694973278⟩⟩
lemma root500_contains : root500.Contains (rootPhase 500) := by
  have hh := CBox.mul_contains root250_contains root250_contains (c:=root500) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def mid501 : CBox := root500
lemma mid501_contains : mid501.Contains (rootPhase 500) := root500_contains
def root501 : CBox := ⟨⟨(-997723066644191609855310120616),(-997723066644191609842094240592)⟩,⟨67443919563664057889098820668,67443919563664057902246110195⟩⟩
lemma root501_contains : root501.Contains (rootPhase 501) := by
  have hh := CBox.mul_contains mid501_contains root1_contains (c:=root501) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def root502 : CBox := ⟨⟨(-998118112900149207131868565520),(-998118112900149207118726394032)⟩,⟨61320736302208577773763491003,61320736302208577786854775764⟩⟩
lemma root502_contains : root502.Contains (rootPhase 502) := by
  have hh := CBox.mul_contains root251_contains root251_contains (c:=root502) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def mid503 : CBox := root502
lemma mid503_contains : mid503.Contains (rootPhase 502) := root502_contains
def root503 : CBox := ⟨⟨(-998475580573294752215298552148),(-998475580573294752202074973340)⟩,⟨55195244349689939800541051132,55195244349689939813732241691⟩⟩
lemma root503_contains : root503.Contains (rootPhase 503) := by
  have hh := CBox.mul_contains mid503_contains root1_contains (c:=root503) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def root504 : CBox := ⟨⟨(-998795456205172392721444081076),(-998795456205172392708326665152)⟩,⟨49067674327418014246109413443,49067674327418014259168110144⟩⟩
lemma root504_contains : root504.Contains (rootPhase 504) := by
  have hh := CBox.mul_contains root252_contains root252_contains (c:=root504) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def mid505 : CBox := root504
lemma mid505_contains : mid505.Contains (rootPhase 504) := root504_contains
def root505 : CBox := ⟨⟨(-999077727752645382895480940772),(-999077727752645382882282556381)⟩,⟨42938256934940823068223842272,42938256934940823081382305131⟩⟩
lemma root505_contains : root505.Contains (rootPhase 505) := by
  have hh := CBox.mul_contains mid505_contains root1_contains (c:=root505) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def root506 : CBox := ⟨⟨(-999322384588349500902867809719),(-999322384588349500889745562363)⟩,⟨36807222941358832315455722334,36807222941358832328556393454⟩⟩
lemma root506_contains : root506.Contains (rootPhase 506) := by
  have hh := CBox.mul_contains root253_contains root253_contains (c:=root506) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def mid507 : CBox := root506
lemma mid507_contains : mid507.Contains (rootPhase 506) := root506_contains
def root507 : CBox := ⟨⟨(-999529417501093163086376477472),(-999529417501093163073173243718)⟩,⟨30674803176636625925089076179,30674803176636625938289551015⟩⟩
lemma root507_contains : root507.Contains (rootPhase 507) := by
  have hh := CBox.mul_contains mid507_contains root1_contains (c:=root507) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def root508 : CBox := ⟨⟨(-999698818696204220122377209640),(-999698818696204220109268775380)⟩,⟨24541228522912288022858385939,24541228522912288035937255286⟩⟩
lemma root508_contains : root508.Contains (rootPhase 508) := by
  have hh := CBox.mul_contains root254_contains root254_contains (c:=root508) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def mid509 : CBox := root508
lemma mid509_contains : mid509.Contains (rootPhase 508) := root508_contains
def root509 : CBox := ⟨⟨(-999830581795823422022359887309),(-999830581795823422009170839820)⟩,⟨18406729905804820918435398641,18406729905804820931613993120⟩⟩
lemma root509_contains : root509.Contains (rootPhase 509) := by
  have hh := CBox.mul_contains mid509_contains root1_contains (c:=root509) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def root510 : CBox := ⟨⟨(-999924701839144540928230461990),(-999924701839144540915120073128)⟩,⟨12271538285719926070502358299,12271538285719926083621289002⟩⟩
lemma root510_contains : root510.Contains (rootPhase 510) := by
  have hh := CBox.mul_contains root255_contains root255_contains (c:=root510) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def mid511 : CBox := root510
lemma mid511_contains : mid511.Contains (rootPhase 510) := root510_contains
def root511 : CBox := ⟨⟨(-999981175282601142663600348327),(-999981175282601142650409340208)⟩,⟨6135884649154475350679727827,6135884649154475363898397720⟩⟩
lemma root511_contains : root511.Contains (rootPhase 511) := by
  have hh := CBox.mul_contains mid511_contains root1_contains (c:=root511) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def root512 : CBox := ⟨⟨(-1000000000000000000006537146143),(-999999999999999999993462813269)⟩,⟨(-8892983621),4181349253⟩⟩
lemma root512_contains : root512.Contains (rootPhase 512) := by
  have hh := CBox.mul_contains root256_contains root256_contains (c:=root512) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def mid513 : CBox := root512
lemma mid513_contains : mid513.Contains (rootPhase 512) := root512_contains
def root513 : CBox := ⟨⟨(-999981175282601142663553153820),(-999981175282601142650398714461)⟩,⟨(-6135884649154475368587534193),(-6135884649154475355413682649)⟩⟩
lemma root513_contains : root513.Contains (rootPhase 513) := by
  have hh := CBox.mul_contains mid513_contains root1_contains (c:=root513) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def root514 : CBox := ⟨⟨(-999924701839144540928235085835),(-999924701839144540914999810957)⟩,⟨(-12271538285719926088410033362),(-12271538285719926075136173067)⟩⟩
lemma root514_contains : root514.Contains (rootPhase 514) := by
  have hh := CBox.mul_contains root257_contains root257_contains (c:=root514) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def mid515 : CBox := root514
lemma mid515_contains : mid515.Contains (rootPhase 514) := root514_contains
def root515 : CBox := ⟨⟨(-999830581795823422022337058750),(-999830581795823422009020216336)⟩,⟨(-18406729905804820936422713410),(-18406729905804820923048350555)⟩⟩
lemma root515_contains : root515.Contains (rootPhase 515) := by
  have hh := CBox.mul_contains mid515_contains root1_contains (c:=root515) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def root516 : CBox := ⟨⟨(-999698818696204220122397092596),(-999698818696204220109017633197)⟩,⟨(-24541228522912288040812445021),(-24541228522912288027403626762)⟩⟩
lemma root516_contains : root516.Contains (rootPhase 516) := by
  have hh := CBox.mul_contains root258_contains root258_contains (c:=root516) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def mid517 : CBox := root516
lemma mid517_contains : mid517.Contains (rootPhase 516) := root516_contains
def root517 : CBox := ⟨⟨(-999529417501093163086361377769),(-999529417501093163072899285715)⟩,⟨(-30674803176636625943153830795),(-30674803176636625929643630635)⟩⟩
lemma root517_contains : root517.Contains (rootPhase 517) := by
  have hh := CBox.mul_contains mid517_contains root1_contains (c:=root517) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def root518 : CBox := ⟨⟨(-999322384588349500902904994596),(-999322384588349500889361532185)⟩,⟨(-36807222941358832333519544170),(-36807222941358832319909454916)⟩⟩
lemma root518_contains : root518.Contains (rootPhase 518) := by
  have hh := CBox.mul_contains root259_contains root259_contains (c:=root518) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def mid519 : CBox := root518
lemma mid519_contains : mid519.Contains (rootPhase 518) := root518_contains
def root519 : CBox := ⟨⟨(-999077727752645382895493221962),(-999077727752645382881865655351)⟩,⟨(-42938256934940823086366596564),(-42938256934940823072654128657)⟩⟩
lemma root519_contains : root519.Contains (rootPhase 519) := by
  have hh := CBox.mul_contains mid519_contains root1_contains (c:=root519) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def root520 : CBox := ⟨⟨(-998795456205172392721490313165),(-998795456205172392707818053915)⟩,⟨(-49067674327418014264209786472),(-49067674327418014250479654997)⟩⟩
lemma root520_contains : root520.Contains (rootPhase 520) := by
  have hh := CBox.mul_contains root260_contains root260_contains (c:=root520) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def mid521 : CBox := root520
lemma mid521_contains : mid521.Contains (rootPhase 520) := root520_contains
def root521 : CBox := ⟨⟨(-998475580573294752215305370780),(-998475580573294752201548033662)⟩,⟨(-55195244349689939818757742933),(-55195244349689939804924453486)⟩⟩
lemma root521_contains : root521.Contains (rootPhase 521) := by
  have hh := CBox.mul_contains mid521_contains root1_contains (c:=root521) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def root522 : CBox := ⟨⟨(-998118112900149207131928119070),(-998118112900149207118088997122)⟩,⟨(-61320736302208577791978374389),(-61320736302208577778045427441)⟩⟩
lemma root522_contains : root522.Contains (rootPhase 522) := by
  have hh := CBox.mul_contains root261_contains root261_contains (c:=root522) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def mid523 : CBox := root522
lemma mid523_contains : mid523.Contains (rootPhase 522) := root522_contains
def root523 : CBox := ⟨⟨(-997723066644191609855347248891),(-997723066644191609841421568401)⟩,⟨(-67443919563664057907391928293),(-67443919563664057893354814984)⟩⟩
lemma root523_contains : root523.Contains (rootPhase 523) := by
  have hh := CBox.mul_contains mid523_contains root1_contains (c:=root523) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def root524 : CBox := ⟨⟨(-997290456678690216142411085419),(-997290456678690216128428420542)⟩,⟨(-73564563599667423538904010903),(-73564563599667423524836226902)⟩⟩
lemma root524_contains : root524.Contains (rootPhase 524) := by
  have hh := CBox.mul_contains root262_contains root262_contains (c:=root524) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def mid525 : CBox := root524
lemma mid525_contains : mid525.Contains (rootPhase 524) := root524_contains
def root525 : CBox := ⟨⟨(-996820299291165714979472037701),(-996820299291165714965401750475)⟩,⟨(-79682437971430121156615013206),(-79682437971430121142442199202)⟩⟩
lemma root525_contains : root525.Contains (rootPhase 525) := by
  have hh := CBox.mul_contains mid525_contains root1_contains (c:=root525) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def root526 : CBox := ⟨⟨(-996312612182778012634094789760),(-996312612182778012619942248884)⟩,⟨(-85797312344439890471103792967),(-85797312344439890456831487189)⟩⟩
lemma root526_contains : root526.Contains (rootPhase 526) := by
  have hh := CBox.mul_contains root263_contains root263_contains (c:=root526) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def mid527 : CBox := root526
lemma mid527_contains : mid527.Contains (rootPhase 526) := root526_contains
def root527 : CBox := ⟨⟨(-995767414467659793989393584577),(-995767414467659793975151930701)⟩,⟨(-91908956497132728634594727478),(-91908956497132728620216370726)⟩⟩
lemma root527_contains : root527.Contains (rootPhase 527) := by
  have hh := CBox.mul_contains mid527_contains root1_contains (c:=root527) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def root528 : CBox := ⟨⟨(-995184726672196886251736005695),(-995184726672196886237461606050)⟩,⟨(-98017140329560602003806420546),(-98017140329560601989420179263)⟩⟩
lemma root528_contains : root528.Contains (rootPhase 528) := by
  have hh := CBox.mul_contains root264_contains root264_contains (c:=root528) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def mid529 : CBox := root528
lemma mid529_contains : mid529.Contains (rootPhase 528) := root528_contains
def root529 : CBox := ⟨⟨(-994564570734255452126035010613),(-994564570734255452111670562510)⟩,⟨(-104121633872054579130611194196),(-104121633872054579116118176825)⟩⟩
lemma root529_contains : root529.Contains (rootPhase 529) := by
  have hh := CBox.mul_contains mid529_contains root1_contains (c:=root529) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def root530 : CBox := ⟨⟨(-993906970002356041553877510484),(-993906970002356041539430489941)⟩,⟨(-110222207293883058817619018290),(-110222207293883058803026817869)⟩⟩
lemma root530_contains : root530.Contains (rootPhase 530) := by
  have hh := CBox.mul_contains root265_contains root265_contains (c:=root530) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def mid531 : CBox := root530
lemma mid531_contains : mid531.Contains (rootPhase 530) := root530_contains
def root531 : CBox := ⟨⟨(-993211949234794533111586080771),(-993211949234794533097047512931)⟩,⟨(-116318630911904767262320976484),(-116318630911904767247620968054)⟩⟩
lemma root531_contains : root531.Contains (rootPhase 531) := by
  have hh := CBox.mul_contains mid531_contains root1_contains (c:=root531) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def root532 : CBox := ⟨⟨(-992479534598709998163762398897),(-992479534598709998149172778766)⟩,⟨(-122410675199216198508497180360),(-122410675199216198493770627550)⟩⟩
lemma root532_contains : root532.Contains (rootPhase 532) := by
  have hh := CBox.mul_contains root266_contains root266_contains (c:=root532) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def mid533 : CBox := root532
lemma mid533_contains : mid533.Contains (rootPhase 532) := root532_contains
def root533 : CBox := ⟨⟨(-991709753669099522867075889484),(-991709753669099522852393662365)⟩,⟨(-128498110793793172634265301079),(-128498110793793172619430094125)⟩⟩
lemma root533_contains : root533.Contains (rootPhase 533) := by
  have hh := CBox.mul_contains mid533_contains root1_contains (c:=root533) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def root534 : CBox := ⟨⟨(-990902635427780025115288918514),(-990902635427780025100523719238)⟩,⟨(-134580708507126186326260186007),(-134580708507126186311326008964)⟩⟩
lemma root534_contains : root534.Contains (rootPhase 534) := by
  have hh := CBox.mul_contains root267_contains root267_contains (c:=root534) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def mid535 : CBox := root534
lemma mid535_contains : mid535.Contains (rootPhase 534) := root534_contains
def root535 : CBox := ⟨⟨(-990058210262297105512989850106),(-990058210262297105498130535566)⟩,⟨(-140658239332849230724747952865),(-140658239332849230709704077487)⟩⟩
lemma root535_contains : root535.Contains (rootPhase 535) := by
  have hh := CBox.mul_contains mid535_contains root1_contains (c:=root535) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def root536 : CBox := ⟨⟨(-989176509964780973458756666206),(-989176509964780973443867020886)⟩,⟨(-146730474455361751668815342605),(-146730474455361751653764015899)⟩⟩
lemma root536_contains : root536.Contains (rootPhase 536) := by
  have hh := CBox.mul_contains root268_contains root268_contains (c:=root536) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def mid537 : CBox := root536
lemma mid537_contains : mid537.Contains (rootPhase 536) := root536_contains
def root537 : CBox := ⟨⟨(-988257567730749491411907335942),(-988257567730749491396922621675)⟩,⟨(-152797185258443427730359319987),(-152797185258443427715197565718)⟩⟩
lemma root537_contains : root537.Contains (rootPhase 537) := by
  have hh := CBox.mul_contains mid537_contains root1_contains (c:=root537) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def root538 : CBox := ⟨⟨(-987301418157858382406956516110),(-987301418157858382391888555174)⟩,⟨(-158858143333861441694459566397),(-158858143333861441679199173812)⟩⟩
lemma root538_contains : root538.Contains (rootPhase 538) := by
  have hh := CBox.mul_contains root269_contains root269_contains (c:=root538) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def mid539 : CBox := root538
lemma mid539_contains : mid539.Contains (rootPhase 538) := root538_contains
def root539 : CBox := ⟨⟨(-986308097244598647870470783566),(-986308097244598647855306237478)⟩,⟨(-164913120489969921428321140527),(-164913120489969921412949265257)⟩⟩
lemma root539_contains : root539.Contains (rootPhase 539) := by
  have hh := CBox.mul_contains mid539_contains root1_contains (c:=root539) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def root540 : CBox := ⟨⟨(-985277642388941244781198321632),(-985277642388941244765988941328)⟩,⟨(-170961888760301226373787388582),(-170961888760301226358393460547)⟩⟩
lemma root540_contains : root540.Contains (rootPhase 540) := by
  have hh := CBox.mul_contains root270_contains root270_contains (c:=root540) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def mid541 : CBox := root540
lemma mid541_contains : mid541.Contains (rootPhase 540) := root540_contains
def root541 : CBox := ⟨⟨(-984210092386929073201087267219),(-984210092386929073185780248796)⟩,⟨(-177004220412148756207042906195),(-177004220412148756191536668231)⟩⟩
lemma root541_contains : root541.Contains (rootPhase 541) := by
  have hh := CBox.mul_contains mid541_contains root1_contains (c:=root541) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def root542 : CBox := ⟨⟨(-983105487431216327187539955010),(-983105487431216327172149362837)⟩,⟨(-183039887955140958526786602799),(-183039887955140958511181988110)⟩⟩
lemma root542_contains : root542.Contains (rootPhase 542) := by
  have hh := CBox.mul_contains root271_contains root271_contains (c:=root542) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def mid543 : CBox := root542
lemma mid543_contains : mid543.Contains (rootPhase 542) := root542_contains
def root543 : CBox := ⟨⟨(-981963869109555264080120630928),(-981963869109555264064630875551)⟩,⟨(-189068664149806212765310220951),(-189068664149806212749592229283)⟩⟩
lemma root543_contains : root543.Contains (rootPhase 543) := by
  have hh := CBox.mul_contains mid543_contains root1_contains (c:=root543) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def root544 : CBox := ⟨⟨(-980785280403230449133446486499),(-980785280403230449117941299564)⟩,⟨(-195090322016128267858596178560),(-195090322016128267842883470502)⟩⟩
lemma root544_contains : root544.Contains (rootPhase 544) := by
  have hh := CBox.mul_contains root272_contains root272_contains (c:=root544) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def mid545 : CBox := root544
lemma mid545_contains : mid545.Contains (rootPhase 544) := root544_contains
def root545 : CBox := ⟨⟨(-979569765685440534446624410491),(-979569765685440534431019164070)⟩,⟨(-201104634842091911568813337683),(-201104634842091911552986595315)⟩⟩
lemma root545_contains : root545.Contains (rootPhase 545) := by
  have hh := CBox.mul_contains mid545_contains root1_contains (c:=root545) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def root546 : CBox := ⟨⟨(-978317370719627633113564250905),(-978317370719627633097875266046)⟩,⟨(-207111376192218549718536150500),(-207111376192218549702611451755)⟩⟩
lemma root546_contains : root546.Contains (rootPhase 546) := by
  have hh := CBox.mul_contains root273_contains root273_contains (c:=root546) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def mid547 : CBox := root546
lemma mid547_contains : mid547.Contains (rootPhase 546) := root546_contains
def root547 : CBox := ⟨⟨(-977028142657754351493225109311),(-977028142657754351477434533079)⟩,⟨(-213110319916091373978236460768),(-213110319916091373962196650607)⟩⟩
lemma root547_contains : root547.Contains (rootPhase 547) := by
  have hh := CBox.mul_contains mid547_contains root1_contains (c:=root547) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def root548 : CBox := ⟨⟨(-975702130038528544467757740168),(-975702130038528544451928840001)⟩,⟨(-219101240156869797238226258002),(-219101240156869797222169216423)⟩⟩
lemma root548_contains : root548.Contains (rootPhase 548) := by
  have hh := CBox.mul_contains root274_contains root274_contains (c:=root548) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def mid549 : CBox := root548
lemma mid549_contains : mid549.Contains (rootPhase 548) := root548_contains
def root549 : CBox := ⟨⟨(-974339382785575860526118838581),(-974339382785575860510187303666)⟩,⟨(-225083911359792836002189836192),(-225083911359792835986016876732)⟩⟩
lemma root549_contains : root549.Contains (rootPhase 549) := by
  have hh := CBox.mul_contains mid549_contains root1_contains (c:=root549) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def root550 : CBox := ⟨⟨(-972939952205560145475143125013),(-972939952205560145459127599963)⟩,⟨(-231058108280671119653833498909),(-231058108280671119637562894255)⟩⟩
lemma root550_contains : root550.Contains (rootPhase 550) := by
  have hh := CBox.mul_contains root275_contains root275_contains (c:=root550) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def mid551 : CBox := root550
lemma mid551_contains : mid551.Contains (rootPhase 550) := root550_contains
def root551 : CBox := ⟨⟨(-971503890986251775544558533147),(-971503890986251775528438833160)⟩,⟨(-237023605994367206878392733992),(-237023605994367206862005122794)⟩⟩
lemma root551_contains : root551.Contains (rootPhase 551) := by
  have hh := CBox.mul_contains mid551_contains root1_contains (c:=root551) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def root552 : CBox := ⟨⟨(-970031253194543992611434211443),(-970031253194543992595299886774)⟩,⟨(-242980179903263889958929551825),(-242980179903263889942546259372)⟩⟩
lemma root552_contains : root552.Contains (rootPhase 552) := by
  have hh := CBox.mul_contains root276_contains root276_contains (c:=root552) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def mid553 : CBox := root552
lemma mid553_contains : mid553.Contains (rootPhase 552) := root552_contains
def root553 : CBox := ⟨⟨(-968522094274417316228574630480),(-968522094274417316212335209065)⟩,⟨(-248927605745720168121397668225),(-248927605745720168104896697701)⟩⟩
lemma root553_contains : root553.Contains (rootPhase 553) := by
  have hh := CBox.mul_contains mid553_contains root1_contains (c:=root553) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def root554 : CBox := ⟨⟨(-966976471044852109094732302176),(-966976471044852109078408767528)⟩,⟨(-254865659604514571564744751441),(-254865659604514571548146572248)⟩⟩
lemma root554_contains : root554.Contains (rootPhase 554) := by
  have hh := CBox.mul_contains root277_contains root277_contains (c:=root554) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def mid555 : CBox := root554
lemma mid555_contains : mid555.Contains (rootPhase 554) := root554_contains
def root555 : CBox := ⟨⟨(-965394441697689374558392943531),(-965394441697689374541962765307)⟩,⟨(-260794117915275518291010279261),(-260794117915275518274293323223)⟩⟩
lemma root555_contains : root555.Contains (rootPhase 555) := by
  have hh := CBox.mul_contains mid555_contains root1_contains (c:=root555) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def root556 : CBox := ⟨⟨(-963776065795439866694012863536),(-963776065795439866677551158388)⟩,⟨(-266712757474898386336116608110),(-266712757474898386319387609627)⟩⟩
lemma root556_contains : root556.Contains (rootPhase 556) := by
  have hh := CBox.mul_contains root278_contains root278_contains (c:=root556) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def mid557 : CBox := root556
lemma mid557_contains : mid557.Contains (rootPhase 556) := root556_contains
def root557 : CBox := ⟨⟨(-962121404269041595437190291464),(-962121404269041595420620911547)⟩,⟨(-272621355449948984504237544581),(-272621355449948984487388984920)⟩⟩
lemma root557_contains : root557.Contains (rootPhase 557) := by
  have hh := CBox.mul_contains mid557_contains root1_contains (c:=root557) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def root558 : CBox := ⟨⟨(-960430519415565811206646857730),(-960430519415565811189993191734)⟩,⟨(-278519689385053105218787101979),(-278519689385053105201841695804)⟩⟩
lemma root558_contains : root558.Contains (rootPhase 558) := by
  have hh := CBox.mul_contains root279_contains root279_contains (c:=root558) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def mid559 : CBox := root558
lemma mid559_contains : mid559.Contains (rootPhase 558) := root558_contains
def root559 : CBox := ⟨⟨(-958703474895871555382295700989),(-958703474895871555365532805687)⟩,⟨(-284407537211271843629309503427),(-284407537211271843612243426143)⟩⟩
lemma root559_contains : root559.Contains (rootPhase 559) := by
  have hh := CBox.mul_contains mid559_contains root1_contains (c:=root559) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def root560 : CBox := ⟨⟨(-956940335732208864943431204358),(-956940335732208864926668588562)⟩,⟨(-290284677254462367647182570477),(-290284677254462367630133616874)⟩⟩
lemma root560_contains : root560.Contains (rootPhase 560) := by
  have hh := CBox.mul_contains root280_contains root280_contains (c:=root560) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def mid561 : CBox := root560
lemma mid561_contains : mid561.Contains (rootPhase 560) := root560_contains
def root561 : CBox := ⟨⟨(-955141168305770721505829597780),(-955141168305770721488956889914)⟩,⟨(-296150888243623824132836716725),(-296150888243623824115666492135)⟩⟩
lemma root561_contains : root561.Contains (rootPhase 561) := by
  have hh := CBox.mul_contains mid561_contains root1_contains (c:=root561) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def root562 : CBox := ⟨⟨(-953306040354193836924437915468),(-953306040354193836907480906795)⟩,⟨(-302005949319228067014561632718),(-302005949319228066997295082528)⟩⟩
lemma root562_contains : root562.Contains (rootPhase 562) := by
  have hh := CBox.mul_contains root281_contains root281_contains (c:=root562) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def mid563 : CBox := root562
lemma mid563_contains : mid563.Contains (rootPhase 562) := root562_contains
def root563 : CBox := ⟨⟨(-951435020969008369556912400213),(-951435020969008369539843739395)⟩,⟨(-307849640041534893693222781005),(-307849640041534893675833840651)⟩⟩
lemma root563_contains : root563.Contains (rootPhase 563) := by
  have hh := CBox.mul_contains mid563_contains root1_contains (c:=root563) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def root564 : CBox := ⟨⟨(-949528180593036667203668577809),(-949528180593036667186575469789)⟩,⟨(-313681740398891476667640676535),(-313681740398891476650245204394)⟩⟩
lemma root564_contains : root564.Contains (rootPhase 564) := by
  have hh := CBox.mul_contains root282_contains root282_contains (c:=root564) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def mid565 : CBox := root564
lemma mid565_contains : mid565.Contains (rootPhase 564) := root564_contains
def root565 : CBox := ⟨⟨(-947585591017741134661159584800),(-947585591017741134643953808468)⟩,⟨(-319502030816015677912740996058),(-319502030816015677895222373399)⟩⟩
lemma root565_contains : root565.Contains (rootPhase 565) := by
  have hh := CBox.mul_contains mid565_contains root1_contains (c:=root565) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def root566 : CBox := ⟨⟨(-945607325380521325738743249787),(-945607325380521325721453081187)⟩,⟨(-325310292162262934147224596276),(-325310292162262934129610061990)⟩⟩
lemma root566_contains : root566.Contains (rootPhase 566) := by
  have hh := CBox.mul_contains root283_contains root283_contains (c:=root566) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def mid567 : CBox := root566
lemma mid567_contains : mid567.Contains (rootPhase 566) := root566_contains
def root567 : CBox := ⟨⟨(-943593458161960361503139808446),(-943593458161960361485735404365)⟩,⟨(-331106305759876401748521862587),(-331106305759876401730783047876)⟩⟩
lemma root567_contains : root567.Contains (rootPhase 567) := by
  have hh := CBox.mul_contains mid567_contains root1_contains (c:=root567) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def root568 : CBox := ⟨⟨(-941544065183020778420329922630),(-941544065183020778402927927235)⟩,⟨(-336889853392220050700574501783),(-336889853392220050682853330318)⟩⟩
lemma root568_contains : root568.Contains (rootPhase 568) := by
  have hh := CBox.mul_contains root284_contains root284_contains (c:=root568) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def mid569 : CBox := root568
lemma mid569_contains : mid569.Contains (rootPhase 568) := root568_contains
def root569 : CBox := ⟨⟨(-939459223602189911970530663919),(-939459223602189911953013555073)⟩,⟨(-342660717311994397604164588862),(-342660717311994397586318530723)⟩⟩
lemma root569_contains : root569.Contains (rootPhase 569) := by
  have hh := CBox.mul_contains mid569_contains root1_contains (c:=root569) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def root570 : CBox := ⟨⟨(-937339011912574923209786510127),(-937339011912574923192185047915)⟩,⟨(-348418680249434568430737638920),(-348418680249434568412796214631)⟩⟩
lemma root570_contains : root570.Contains (rootPhase 570) := by
  have hh := CBox.mul_contains root285_contains root285_contains (c:=root570) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def mid571 : CBox := root570
lemma mid571_contains : mid571.Contains (rootPhase 570) := root570_contains
def root571 : CBox := ⟨⟨(-935183509938947577650136042945),(-935183509938947577632417894839)⟩,⟨(-354163525420490382368886509863),(-354163525420490382350819059817)⟩⟩
lemma root571_contains : root571.Contains (rootPhase 571) := by
  have hh := CBox.mul_contains mid571_contains root1_contains (c:=root571) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def root572 : CBox := ⟨⟨(-932992798834738887719580645024),(-932992798834738887701845415817)⟩,⟨(-359895036534988148786594153494),(-359895036534988148768526042799)⟩⟩
lemma root572_contains : root572.Contains (rootPhase 572) := by
  have hh := CBox.mul_contains root286_contains root286_contains (c:=root572) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def mid573 : CBox := root572
lemma mid573_contains : mid573.Contains (rootPhase 572) := root572_contains
def root573 : CBox := ⟨⟨(-930766961078983731952834840222),(-930766961078983731934981926598)⟩,⟨(-365612997804773870023297294475),(-365612997804773870005102423072)⟩⟩
lemma root573_contains : root573.Contains (rootPhase 573) := by
  have hh := CBox.mul_contains mid573_contains root1_contains (c:=root573) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def root574 : CBox := ⟨⟨(-928506080473215565945155328686),(-928506080473215565927218054818)⟩,⟨(-371317193951837543423532113753),(-371317193951837543405242343248)⟩⟩
lemma root574_contains : root574.Contains (rootPhase 574) := by
  have hh := CBox.mul_contains root287_contains root287_contains (c:=root574) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def mid575 : CBox := root574
lemma mid575_contains : mid575.Contains (rootPhase 574) := root574_contains
def root575 : CBox := ⟨⟨(-926210242138311341982824190011),(-926210242138311341964767652820)⟩,⟨(-377007410216418256738227122981),(-377007410216418256719809442414)⟩⟩
lemma root575_contains : root575.Contains (rootPhase 575) := by
  have hh := CBox.mul_contains mid575_contains root1_contains (c:=root575) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def root576 : CBox := ⟨⟨(-923879532511286756136186577759),(-923879532511286756118151311406)⟩,⟨(-382683432365089771740100174716),(-382683432365089771721716881342)⟩⟩
lemma root576_contains : root576.Contains (rootPhase 576) := by
  have hh := CBox.mul_contains root288_contains root288_contains (c:=root576) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def mid577 : CBox := root576
lemma mid577_contains : mid577.Contains (rootPhase 576) := root576_contains
def root577 : CBox := ⟨⟨(-921514039342041943473442956550),(-921514039342041943455287633353)⟩,⟨(-388345046698826291636695912353),(-388345046698826291618184198341)⟩⟩
lemma root577_contains : root577.Contains (rootPhase 577) := by
  have hh := CBox.mul_contains mid577_contains root1_contains (c:=root577) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def root578 : CBox := ⟨⟨(-919113851690057743916549708591),(-919113851690057743898310186936)⟩,⟨(-393992040061048108607936017348),(-393992040061048108589330047063)⟩⟩
lemma root578_contains : root578.Contains (rootPhase 578) := by
  have hh := CBox.mul_contains root289_contains root289_contains (c:=root578) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def mid579 : CBox := root578
lemma mid579_contains : mid579.Contains (rootPhase 578) := root578_contains
def root579 : CBox := ⟨⟨(-916679059921042663124572935053),(-916679059921042663106211773704)⟩,⟨(-399624199845646828555926918598),(-399624199845646828537191370242)⟩⟩
lemma root579_contains : root579.Contains (rootPhase 579) := by
  have hh := CBox.mul_contains mid579_contains root1_contains (c:=root579) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def root580 : CBox := ⟨⟨(-914209755703530654643118647168),(-914209755703530654624748035302)⟩,⟨(-405241314004989870920286067315),(-405241314004989870901556026761)⟩⟩
lemma root580_contains : root580.Contains (rootPhase 580) := by
  have hh := CBox.mul_contains root290_contains root290_contains (c:=root580) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def mid581 : CBox := root580
lemma mid581_contains : mid581.Contains (rootPhase 580) := root580_contains
def root581 : CBox := ⟨⟨(-911706032005429851412545611679),(-911706032005429851394052382108)⟩,⟨(-410843171057903942195334092713),(-410843171057903942176473766444)⟩⟩
lemma root581_contains : root581.Contains (rootPhase 581) := by
  have hh := CBox.mul_contains mid581_contains root1_contains (c:=root581) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def root582 : CBox := ⟨⟨(-909167983090522376572058283513),(-909167983090522376553480935234)⟩,⟨(-416429560097637182574510594533),(-416429560097637182555556532657)⟩⟩
lemma root582_contains : root582.Contains (rootPhase 582) := by
  have hh := CBox.mul_contains root291_contains root291_contains (c:=root582) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def mid583 : CBox := root582
lemma mid583_contains : mid583.Contains (rootPhase 582) := root582_contains
def root583 : CBox := ⟨⟨(-906595704514915365341179327912),(-906595704514915365322477773263)⟩,⟨(-422000270799799685953262634523),(-422000270799799685934177119711)⟩⟩
lemma root583_contains : root583.Contains (rootPhase 583) := by
  have hh := CBox.mul_contains mid583_contains root1_contains (c:=root583) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def root584 : CBox := ⟨⟨(-903989293123443331594391814941),(-903989293123443331575710967702)⟩,⟨(-427555093430282094332922487662),(-427555093430282094313869432861)⟩⟩
lemma root584_contains : root584.Contains (rootPhase 584) := by
  have hh := CBox.mul_contains root292_contains root292_contains (c:=root584) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def mid585 : CBox := root584
lemma mid585_contains : mid585.Contains (rootPhase 584) := root584_contains
def root585 : CBox := ⟨⟨(-901348847046022014578983249474),(-901348847046022014560177373660)⟩,⟨(-433093818853151968496241314443),(-433093818853151968477056273268)⟩⟩
lemma root585_contains : root585.Contains (rootPhase 585) := by
  have hh := CBox.mul_contains mid585_contains root1_contains (c:=root585) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def root586 : CBox := ⟨⟨(-898674465693953843050238971373),(-898674465693953843031349186832)⟩,⟨(-438616238538527637659087888606),(-438616238538527637639809769605)⟩⟩
lemma root586_contains : root586.Contains (rootPhase 586) := by
  have hh := CBox.mul_contains root293_contains root293_contains (c:=root586) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def mid587 : CBox := root586
lemma mid587_contains : mid587.Contains (rootPhase 586) := root586_contains
def root587 : CBox := ⟨⟨(-895966249756185155922868931067),(-895966249756185155903852525449)⟩,⟨(-444122144570429231654194970106),(-444122144570429231634783689378)⟩⟩
lemma root587_contains : root587.Contains (rootPhase 587) := by
  have hh := CBox.mul_contains mid587_contains root1_contains (c:=root587) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def root588 : CBox := ⟨⟨(-893224301195515320350708967881),(-893224301195515320331691030669)⟩,⟨(-449611329654606600058410816478),(-449611329654606600039011573914)⟩⟩
lemma root588_contains : root588.Contains (rootPhase 588) := by
  have hh := CBox.mul_contains root294_contains root294_contains (c:=root588) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def mid589 : CBox := root588
lemma mid589_contains : mid589.Contains (rootPhase 588) := root588_contains
def root589 : CBox := ⟨⟨(-890448723244757889960489969173),(-890448723244757889941344455937)⟩,⟨(-455083587126343823548049012941),(-455083587126343823528515929679)⟩⟩
lemma root589_contains : root589.Contains (rootPhase 589) := by
  have hh := CBox.mul_contains mid589_contains root1_contains (c:=root589) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def root590 : CBox := ⟨⟨(-887639620402853947768545993100),(-887639620402853947749316740640)⟩,⟨(-460538710958240023645403954007),(-460538710958240023625778368482)⟩⟩
lemma root590_contains : root590.Contains (rootPhase 590) := by
  have hh := CBox.mul_contains root295_contains root295_contains (c:=root590) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def mid591 : CBox := root590
lemma mid591_contains : mid591.Contains (rootPhase 590) := root590_contains
def root591 : CBox := ⟨⟨(-884797098430937780112419097267),(-884797098430937780093060671127)⟩,⟨(-465976495767966177915042399178),(-465976495767966177895281788326)⟩⟩
lemma root591_contains : root591.Contains (rootPhase 591) := by
  have hh := CBox.mul_contains mid591_contains root1_contains (c:=root591) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def root592 : CBox := ⟨⟨(-881921264348355029721132649221),(-881921264348355029701812948750)⟩,⟨(-471396736825997648568645958737),(-471396736825997648548933825721)⟩⟩
lemma root592_contains : root592.Contains (rootPhase 592) := by
  have hh := CBox.mul_contains root296_contains root296_contains (c:=root592) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def mid593 : CBox := root592
lemma mid593_contains : mid593.Contains (rootPhase 592) := root592_contains
def root593 : CBox := ⟨⟨(-879012226428633477839747543941),(-879012226428633477820297929001)⟩,⟨(-476799230063322133354480304817),(-476799230063322133334632703462)⟩⟩
lemma root593_contains : root593.Contains (rootPhase 593) := by
  have hh := CBox.mul_contains mid593_contains root1_contains (c:=root593) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def root594 : CBox := ⟨⟨(-876070094195406607104292896866),(-876070094195406607084759870044)⟩,⟨(-482183772079122748529708548843),(-482183772079122748509769192565)⟩⟩
lemma root594_contains : root594.Contains (rootPhase 594) := by
  have hh := CBox.mul_contains root297_contains root297_contains (c:=root594) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def mid595 : CBox := root594
lemma mid595_contains : mid595.Contains (rootPhase 594) := root594_contains
def root595 : CBox := ⟨⟨(-873094978418290098644583448792),(-873094978418290098624918907259)⟩,⟨(-487550160148435954653913311193),(-487550160148435954633837294850)⟩⟩
lemma root595_contains : root595.Contains (rootPhase 595) := by
  have hh := CBox.mul_contains mid595_contains root1_contains (c:=root595) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def root596 : CBox := ⟨⟨(-870086991108711418660769651223),(-870086991108711418641111749052)⟩,⟨(-492898192229784036885441313874),(-492898192229784036865384151646)⟩⟩
lemma root596_contains : root596.Contains (rootPhase 596) := by
  have hh := CBox.mul_contains root298_contains root298_contains (c:=root596) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def mid597 : CBox := root596
lemma mid597_contains : mid597.Contains (rootPhase 596) := root596_contains
def root597 : CBox := ⟨⟨(-867046245515692651488722190612),(-867046245515692651468931844632)⟩,⟨(-498227666972781852423462799364),(-498227666972781852403268328598)⟩⟩
lemma root597_contains : root597.Contains (rootPhase 597) := by
  have hh := CBox.mul_contains mid597_contains root1_contains (c:=root597) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def root598 : CBox := ⟨⟨(-863972856121586737926698285911),(-863972856121586737906824789116)⟩,⟨(-503538383725717558704387096093),(-503538383725717558684101501304)⟩⟩
lemma root598_contains : root598.Contains (rootPhase 598) := by
  have hh := CBox.mul_contains root299_contains root299_contains (c:=root598) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def mid599 : CBox := root598
lemma mid599_contains : mid599.Contains (rootPhase 598) := root598_contains
def root599 : CBox := ⟨⟨(-860866938637767279353185231042),(-860866938637767279333177685723)⟩,⟨(-508830142543107036944334018568),(-508830142543107036923909914778)⟩⟩
lemma root599_contains : root599.Contains (rootPhase 599) := by
  have hh := CBox.mul_contains mid599_contains root1_contains (c:=root599) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def root600 : CBox := ⟨⟨(-857728610000272069910834319234),(-857728610000272069890867017745)⟩,⟨(-514102744193221726606249453619),(-514102744193221726585874102604)⟩⟩
lemma root600_contains : root600.Contains (rootPhase 600) := by
  have hh := CBox.mul_contains root300_contains root300_contains (c:=root600) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def mid601 : CBox := root600
lemma mid601_contains : mid601.Contains (rootPhase 600) := root600_contains
def root601 : CBox := ⟨⟨(-854557988365400520776477119850),(-854557988365400520756375015230)⟩,⟨(-519355990165589587374450206502),(-519355990165589587353935893253)⟩⟩
lemma root601_contains : root601.Contains (rootPhase 601) := by
  have hh := CBox.mul_contains mid601_contains root1_contains (c:=root601) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def root602 : CBox := ⟨⟨(-851355193105265142269929650139),(-851355193105265142249744783840)⟩,⟨(-524589682678468906227758974170),(-524589682678468906207154309961)⟩⟩
lemma root602_contains : root602.Contains (rootPhase 602) := by
  have hh := CBox.mul_contains root301_contains root301_contains (c:=root602) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def mid603 : CBox := root602
lemma mid603_contains : mid603.Contains (rootPhase 602) := root602_contains
def root603 : CBox := ⟨⟨(-848120344803297251287824226530),(-848120344803297251267502950047)⟩,⟨(-529803624686294668228780208254),(-529803624686294668208035374363)⟩⟩
lemma root603_contains : root603.Contains (rootPhase 603) := by
  have hh := CBox.mul_contains mid603_contains root1_contains (c:=root603) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def root604 : CBox := ⟨⟨(-844853565249707073268237450293),(-844853565249707073247931265658)⟩,⟨(-534997619887097210675784257268),(-534997619887097210655065439012)⟩⟩
lemma root604_contains : root604.Contains (rootPhase 604) := by
  have hh := CBox.mul_contains root302_contains root302_contains (c:=root604) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def mid605 : CBox := root604
lemma mid605_contains : mid605.Contains (rootPhase 604) := root604_contains
def root605 : CBox := ⟨⟨(-841554977436898409612217556278),(-841554977436898409591774060759)⟩,⟨(-540171472729892881310617930305),(-540171472729892881289758325823)⟩⟩
lemma root605_contains : root605.Contains (rootPhase 605) := by
  have hh := CBox.mul_contains mid605_contains root1_contains (c:=root605) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def root606 : CBox := ⟨⟨(-838224705554838043195739240295),(-838224705554838043175213338468)⟩,⟨(-545324988422046422326799215682),(-545324988422046422305849947568)⟩⟩
lemma root606_contains : root606.Contains (rootPhase 606) := by
  have hh := CBox.mul_contains root303_contains root303_contains (c:=root606) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def mid607 : CBox := root606
lemma mid607_contains : mid607.Contains (rootPhase 606) := root606_contains
def root607 : CBox := ⟨⟨(-834862874986380056313196383200),(-834862874986380056292531559652)⟩,⟨(-550457972936604802990167229296),(-550457972936604802969075959335)⟩⟩
lemma root607_contains : root607.Contains (rootPhase 607) := by
  have hh := CBox.mul_contains mid607_contains root1_contains (c:=root607) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def root608 : CBox := ⟨⟨(-831469612302545237087535359618),(-831469612302545237066932903512)⟩,⟨(-555570233019602224755668065037),(-555570233019602224734645663381)⟩⟩
lemma root608_contains : root608.Contains (rootPhase 608) := by
  have hh := CBox.mul_contains root304_contains root304_contains (c:=root608) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def mid609 : CBox := root608
lemma mid609_contains : mid609.Contains (rootPhase 608) := root608_contains
def root609 : CBox := ⟨⟨(-828045045257755752076327535232),(-828045045257755752055585510771)⟩,⟨(-560661576197336023852612873516),(-560661576197336023831448132339)⟩⟩
lemma root609_contains : root609.Contains (rootPhase 609) := by
  have hh := CBox.mul_contains mid609_contains root1_contains (c:=root609) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def root610 : CBox := ⟨⟨(-824589302785025264483627814556),(-824589302785025264462803900817)⟩,⟨(-565731810783613197402706167672),(-565731810783613197381452635642)⟩⟩
lemma root610_contains : root610.Contains (rootPhase 610) := by
  have hh := CBox.mul_contains root305_contains root305_contains (c:=root610) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def mid611 : CBox := root610
lemma mid611_contains : mid611.Contains (rootPhase 610) := root610_contains
def root611 : CBox := ⟨⟨(-821102514991104679069308690578),(-821102514991104679048343596780)⟩,⟨(-570780745886967280245659792051),(-570780745886967280224262699147)⟩⟩
lemma root611_contains : root611.Contains (rootPhase 611) := by
  have hh := CBox.mul_contains mid611_contains root1_contains (c:=root611) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def root612 : CBox := ⟨⟨(-817584813151583696513770087609),(-817584813151583696492828760951)⟩,⟨(-575808191417845300758956540427),(-575808191417845300737592875208)⟩⟩
lemma root612_contains : root612.Contains (rootPhase 612) := by
  have hh := CBox.mul_contains root306_contains root306_contains (c:=root612) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def mid613 : CBox := root612
lemma mid613_contains : mid613.Contains (rootPhase 612) := root612_contains
def root613 : CBox := ⟨⟨(-814036329705948361663420149656),(-814036329705948361642336773381)⟩,⟨(-580813958095764545088645183215),(-580813958095764545067137374337)⟩⟩
lemma root613_contains : root613.Contains (rootPhase 613) := by
  have hh := CBox.mul_contains mid613_contains root1_contains (c:=root613) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def root614 : CBox := ⟨⟨(-810457198252594791735630860802),(-810457198252594791714466046140)⟩,⟨(-585797857456438860341168407025),(-585797857456438860319572551119)⟩⟩
lemma root614_contains : root614.Contains (rootPhase 614) := by
  have hh := CBox.mul_contains root307_contains root307_contains (c:=root614) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def mid615 : CBox := root614
lemma mid615_contains : mid615.Contains (rootPhase 614) := root614_contains
def root615 : CBox := ⟨⟨(-806847553543799272215496835209),(-806847553543799272194188356147)⟩,⟨(-590759701858874228437041678039),(-590759701858874228415300449539)⟩⟩
lemma root615_contains : root615.Contains (rootPhase 615) := by
  have hh := CBox.mul_contains mid615_contains root1_contains (c:=root615) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def root616 : CBox := ⟨⟨(-803207531480644909815611858589),(-803207531480644909794364296322)⟩,⟨(-595699304492433343480150483829),(-595699304492433343458475675403)⟩⟩
lemma root616_contains : root616.Contains (rootPhase 616) := by
  have hh := CBox.mul_contains root308_contains root308_contains (c:=root616) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def mid617 : CBox := root616
lemma mid617_contains : mid617.Contains (rootPhase 616) := root616_contains
def root617 : CBox := ⟨⟨(-799537269107905033509237047337),(-799537269107905033487845145231)⟩,⟨(-600616479383868926667055995681),(-600616479383868926645235448804)⟩⟩
lemma root617_contains : root617.Contains (rootPhase 617) := by
  have hh := CBox.mul_contains mid617_contains root1_contains (c:=root617) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def root618 : CBox := ⟨⟨(-795836904608883536271806481098),(-795836904608883536250333715112)⟩,⟨(-605511041404325513933843776375),(-605511041404325513911936072754)⟩⟩
lemma root618_contains : root618.Contains (rootPhase 618) := by
  have hh := CBox.mul_contains root309_contains root309_contains (c:=root618) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def mid619 : CBox := root618
lemma mid619_contains : mid619.Contains (rootPhase 618) := root618_contains
def root619 : CBox := ⟨⟨(-792106577300212351791413760419),(-792106577300212351769795039031)⟩,⟨(-610382806276309452729635510498),(-610382806276309452707580833749)⟩⟩
lemma root619_contains : root619.Contains (rootPhase 619) := by
  have hh := CBox.mul_contains mid619_contains root1_contains (c:=root619) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def root620 : CBox := ⟨⟨(-788346427626606262018202582911),(-788346427626606261996616588438)⟩,⟨(-615231590580626845498169247690),(-615231590580626845476155755396)⟩⟩
lemma root620_contains : root620.Contains (rootPhase 620) := by
  have hh := CBox.mul_contains root310_contains root310_contains (c:=root620) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def mid621 : CBox := root620
lemma mid621_contains : mid621.Contains (rootPhase 620) := root620_contains
def root621 : CBox := ⟨⟨(-784556597155575233032987228646),(-784556597155575233011254442809)⟩,⟨(-620057211763289178659590434310),(-620057211763289178637429421239)⟩⟩
lemma root621_contains : root621.Contains (rootPhase 621) := by
  have hh := CBox.mul_contains mid621_contains root1_contains (c:=root621) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def root622 : CBox := ⟨⟨(-780737228572094478310706698383),(-780737228572094478288893597708)⟩,⟨(-624859488142386377097430915854),(-624859488142386377075183547479)⟩⟩
lemma root622_contains : root622.Contains (rootPhase 622) := by
  have hh := CBox.mul_contains root311_contains root311_contains (c:=root622) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def mid623 : CBox := root622
lemma mid623_contains : mid623.Contains (rootPhase 622) := root622_contains
def root623 : CBox := ⟨⟨(-776888465673232450050003828685),(-776888465673232450028042318723)⟩,⟨(-629638238914927025386406381014),(-629638238914927025364010250216)⟩⟩
lemma root623_contains : root623.Contains (rootPhase 623) := by
  have hh := CBox.mul_contains mid623_contains root1_contains (c:=root623) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def root624 : CBox := ⟨⟨(-773010453362736960820024842086),(-773010453362736960798145459838)⟩,⟨(-634393284163645498228546205512),(-634393284163645498206235850984)⟩⟩
lemma root624_contains : root624.Contains (rootPhase 624) := by
  have hh := CBox.mul_contains root312_contains root312_contains (c:=root624) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def mid625 : CBox := root624
lemma mid625_contains : mid625.Contains (rootPhase 624) := root624_contains
def root625 : CBox := ⟨⟨(-769103337645579639355802266537),(-769103337645579639333773904467)⟩,⟨(-639124444863775743814929614902),(-639124444863775743792470242200)⟩⟩
lemma root625_contains : root625.Contains (rootPhase 625) := by
  have hh := CBox.mul_contains mid625_contains root1_contains (c:=root625) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def root626 : CBox := ⟨⟨(-765167265622458925898015507242),(-765167265622458925875907526600)⟩,⟨(-643831542889791465081562373159),(-643831542889791465059017627468)⟩⟩
lemma root626_contains : root626.Contains (rootPhase 626) := by
  have hh := CBox.mul_contains root313_contains root313_contains (c:=root626) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def mid627 : CBox := root626
lemma mid627_contains : mid627.Contains (rootPhase 626) := root626_contains
def root627 : CBox := ⟨⟨(-761202385484261814038968170087),(-761202385484261814016709592305)⟩,⟨(-648514401022112445098104075048),(-648514401022112445075409064987)⟩⟩
lemma root627_contains : root627.Contains (rootPhase 627) := by
  have hh := CBox.mul_contains mid627_contains root1_contains (c:=root627) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def root628 : CBox := ⟨⟨(-757208846506484547584684996957),(-757208846506484547562468312202)⟩,⟨(-653172842953776764097713913461),(-653172842953776764075068077716)⟩⟩
lemma root628_contains : root628.Contains (rootPhase 628) := by
  have hh := CBox.mul_contains root314_contains root314_contains (c:=root628) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def mid629 : CBox := root628
lemma mid629_contains : mid629.Contains (rootPhase 628) := root628_contains
def root629 : CBox := ⟨⟨(-753186799043612482492710711000),(-753186799043612482470342629360)⟩,⟨(-657806693297078656944760394601),(-657806693297078656921963783704)⟩⟩
lemma root629_contains : root629.Contains (rootPhase 629) := by
  have hh := CBox.mul_contains mid629_contains root1_contains (c:=root629) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def root630 : CBox := ⟨⟨(-749136394523459325478506580120),(-749136394523459325456059528027)⟩,⟨(-662415777590171761126681929097),(-662415777590171761103800804219)⟩⟩
lemma root630_contains : root630.Contains (rootPhase 630) := by
  have hh := CBox.mul_contains root315_contains root315_contains (c:=root630) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def mid631 : CBox := root630
lemma mid631_contains : mid631.Contains (rootPhase 630) := root630_contains
def root631 : CBox := ⟨⟨(-745057785441465962417270784271),(-745057785441465962394670716344)⟩,⟨(-666999922303637506663833952889),(-666999922303637506640800800332)⟩⟩
lemma root631_contains : root631.Contains (rootPhase 631) := by
  have hh := CBox.mul_contains mid631_contains root1_contains (c:=root631) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def root632 : CBox := ⟨⟨(-740951125354959091184922705113),(-740951125354959091162405317113)⟩,⟨(-671558954847018400639005355752),(-671558954847018400616057626757)⟩⟩
lemma root632_contains : root632.Contains (rootPhase 632) := by
  have hh := CBox.mul_contains root316_contains root316_contains (c:=root632) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def mid633 : CBox := root632
lemma mid633_contains : mid633.Contains (rootPhase 632) := root632_contains
def root633 : CBox := ⟨⟨(-736816568877369875099498833454),(-736816568877369875076827844656)⟩,⟨(-676092703575315960374115249569),(-676092703575315960351015221345)⟩⟩
lemma root633_contains : root633.Contains (rootPhase 633) := by
  have hh := CBox.mul_contains mid633_contains root1_contains (c:=root633) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def root634 : CBox := ⟨⟨(-732654271672412834624935802778),(-732654271672412834602186608384)⟩,⟨(-680600997795453050608159486864),(-680600997795453050584975953645)⟩⟩
lemma root634_contains : root634.Contains (rootPhase 634) := by
  have hh := CBox.mul_contains root317_contains root317_contains (c:=root634) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def mid635 : CBox := root634
lemma mid635_contains : mid635.Contains (rootPhase 634) := root634_contains
def root635 : CBox := ⟨⟨(-728464390448225196501485972032),(-728464390448225196478581558713)⟩,⟨(-685083667772700381375849474471),(-685083667772700381352512385088)⟩⟩
lemma root635_contains : root635.Contains (rootPhase 635) := by
  have hh := CBox.mul_contains mid635_contains root1_contains (c:=root635) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def root636 : CBox := ⟨⟨(-724247082951466920950477917898),(-724247082951466920927624835229)⟩,⟨(-689540544737066924630489827060),(-689540544737066924607210223235)⟩⟩
lemma root636_contains : root636.Contains (rootPhase 636) := by
  have hh := CBox.mul_contains root318_contains root318_contains (c:=root636) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def mid637 : CBox := root636
lemma mid637_contains : mid637.Contains (rootPhase 636) := root636_contains
def root637 : CBox := ⟨⟨(-720002507961381629086153503906),(-720002507961381629063144441184)⟩,⟨(-693971460889654009017561492014),(-693971460889654008994127859520)⟩⟩
lemma root637_contains : root637.Contains (rootPhase 637) := by
  have hh := CBox.mul_contains mid637_contains root1_contains (c:=root637) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def root638 : CBox := ⟨⟨(-715730825283818654135025733103),(-715730825283818654111939214154)⟩,⟨(-698376249408972853568672672743),(-698376249408972853545156452718)⟩⟩
lemma root638_contains : root638.Contains (rootPhase 638) := by
  have hh := CBox.mul_contains root319_contains root319_contains (c:=root638) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def mid639 : CBox := root638
lemma mid639_contains : mid639.Contains (rootPhase 638) := root638_contains
def root639 : CBox := ⟨⟨(-711432195745216441531686112144),(-711432195745216441508441994125)⟩,⟨(-702754744457225302466841890598),(-702754744457225302443170379298)⟩⟩
lemma root639_contains : root639.Contains (rootPhase 639) := by
  have hh := CBox.mul_contains mid639_contains root1_contains (c:=root639) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def root640 : CBox := ⟨⟨(-707106781186547524410329403981),(-707106781186547524387194748638)⟩,⟨(-707106781186547524414707195255),(-707106781186547524391146028847)⟩⟩
lemma root640_contains : root640.Contains (rootPhase 640) := by
  have hh := CBox.mul_contains root320_contains root320_contains (c:=root640) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def mid641 : CBox := root640
lemma mid641_contains : mid641.Contains (rootPhase 640) := root640_contains
def root641 : CBox := ⟨⟨(-702754744457225302462462473773),(-702754744457225302439169774987)⟩,⟨(-711432195745216441536061249748),(-711432195745216441512344664949)⟩⟩
lemma root641_contains : root641.Contains (rootPhase 641) := by
  have hh := CBox.mul_contains mid641_contains root1_contains (c:=root641) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def root642 : CBox := ⟨⟨(-698376249408972853564383864628),(-698376249408972853541014605661)⟩,⟨(-715730825283818654139494620733),(-715730825283818654115696560168)⟩⟩
lemma root642_contains : root642.Contains (rootPhase 642) := by
  have hh := CBox.mul_contains root321_contains root321_contains (c:=root642) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def mid643 : CBox := root642
lemma mid643_contains : mid643.Contains (rootPhase 642) := root642_contains
def root643 : CBox := ⟨⟨(-693971460889654009013368649341),(-693971460889654008989839730395)⟩,⟨(-720002507961381629090713519370),(-720002507961381629066758774865)⟩⟩
lemma root643_contains : root643.Contains (rootPhase 643) := by
  have hh := CBox.mul_contains mid643_contains root1_contains (c:=root643) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def root644 : CBox := ⟨⟨(-689540544737066924626318536220),(-689540544737066924602850544955)⟩,⟨(-724247082951466920955056838675),(-724247082951466920931168071336)⟩⟩
lemma root644_contains : root644.Contains (rootPhase 644) := by
  have hh := CBox.mul_contains root322_contains root322_contains (c:=root644) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def mid645 : CBox := root644
lemma mid645_contains : mid645.Contains (rootPhase 644) := root644_contains
def root645 : CBox := ⟨⟨(-685083667772700381371704792770),(-685083667772700381348076421541)⟩,⟨(-728464390448225196506091536697),(-728464390448225196482045652878)⟩⟩
lemma root645_contains : root645.Contains (rootPhase 645) := by
  have hh := CBox.mul_contains mid645_contains root1_contains (c:=root645) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def root646 : CBox := ⟨⟨(-680600997795453050604104761409),(-680600997795453050580400680776)⟩,⟨(-732654271672412834629632826168),(-732654271672412834605506441951)⟩⟩
lemma root646_contains : root646.Contains (rootPhase 646) := by
  have hh := CBox.mul_contains root323_contains root323_contains (c:=root646) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def mid647 : CBox := root646
lemma mid647_contains : mid647.Contains (rootPhase 646) := root646_contains
def root647 : CBox := ⟨⟨(-676092703575315960370158760852),(-676092703575315960346292683577)⟩,⟨(-736816568877369875104287601299),(-736816568877369875080002830063)⟩⟩
lemma root647_contains : root647.Contains (rootPhase 647) := by
  have hh := CBox.mul_contains mid647_contains root1_contains (c:=root647) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def root648 : CBox := ⟨⟨(-671558954847018400635047974707),(-671558954847018400611287279922)⟩,⟨(-740951125354959091189708764375),(-740951125354959091165529607562)⟩⟩
lemma root648_contains : root648.Contains (rootPhase 648) := by
  have hh := CBox.mul_contains root324_contains root324_contains (c:=root648) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def mid649 : CBox := root648
lemma mid649_contains : mid649.Contains (rootPhase 648) := root648_contains
def root649 : CBox := ⟨⟨(-666999922303637506659890913832),(-666999922303637506635967738701)⟩,⟨(-745057785441465962422067931779),(-745057785441465962397730217185)⟩⟩
lemma root649_contains : root649.Contains (rootPhase 649) := by
  have hh := CBox.mul_contains mid649_contains root1_contains (c:=root649) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def root650 : CBox := ⟨⟨(-662415777590171761122828258398),(-662415777590171761098830331846)⟩,⟨(-749136394523459325483392923220),(-749136394523459325458975836115)⟩⟩
lemma root650_contains : root650.Contains (rootPhase 650) := by
  have hh := CBox.mul_contains root325_contains root325_contains (c:=root650) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def mid651 : CBox := root650
lemma mid651_contains : mid651.Contains (rootPhase 650) := root650_contains
def root651 : CBox := ⟨⟨(-657806693297078656941007173095),(-657806693297078656916845151980)⟩,⟨(-753186799043612482497689309522),(-753186799043612482473112391102)⟩⟩
lemma root651_contains : root651.Contains (rootPhase 651) := by
  have hh := CBox.mul_contains mid651_contains root1_contains (c:=root651) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def root652 : CBox := ⟨⟨(-653172842953776764093976988424),(-653172842953776764069885773385)⟩,⟨(-757208846506484547589674605507),(-757208846506484547565172481267)⟩⟩
lemma root652_contains : root652.Contains (rootPhase 652) := by
  have hh := CBox.mul_contains root326_contains root326_contains (c:=root652) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def mid653 : CBox := root652
lemma mid653_contains : mid653.Contains (rootPhase 652) := root652_contains
def root653 : CBox := ⟨⟨(-648514401022112445094401428256),(-648514401022112445070145442081)⟩,⟨(-761202385484261814043989507239),(-761202385484261814019327160456)⟩⟩
lemma root653_contains : root653.Contains (rootPhase 653) := by
  have hh := CBox.mul_contains mid653_contains root1_contains (c:=root653) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def root654 : CBox := ⟨⟨(-643831542889791465077948405732),(-643831542889791465053618622441)⟩,⟨(-765167265622458925903123732122),(-765167265622458925878383047107)⟩⟩
lemma root654_contains : root654.Contains (rootPhase 654) := by
  have hh := CBox.mul_contains root327_contains root327_contains (c:=root654) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def mid655 : CBox := root654
lemma mid655_contains : mid655.Contains (rootPhase 654) := root654_contains
def root655 : CBox := ⟨⟨(-639124444863775743811418344628),(-639124444863775743786922176600)⟩,⟨(-769103337645579639361003328164),(-769103337645579639336101142783)⟩⟩
lemma root655_contains : root655.Contains (rootPhase 655) := by
  have hh := CBox.mul_contains mid655_contains root1_contains (c:=root655) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def root656 : CBox := ⟨⟨(-634393284163645498225021550674),(-634393284163645498200655147595)⟩,⟨(-773010453362736960825208352440),(-773010453362736960800434520548)⟩⟩
lemma root656_contains : root656.Contains (rootPhase 656) := by
  have hh := CBox.mul_contains root328_contains root328_contains (c:=root656) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def mid657 : CBox := root656
lemma mid657_contains : mid657.Contains (rootPhase 656) := root656_contains
def root657 : CBox := ⟨⟨(-629638238914927025382899368021),(-629638238914927025358366225463)⟩,⟨(-776888465673232450055199040580),(-776888465673232450030263667676)⟩⟩
lemma root657_contains : root657.Contains (rootPhase 657) := by
  have hh := CBox.mul_contains mid657_contains root1_contains (c:=root657) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def root658 : CBox := ⟨⟨(-624859488142386377094011975753),(-624859488142386377069406114840)⟩,⟨(-780737228572094478315986529785),(-780737228572094478290974037704)⟩⟩
lemma root658_contains : root658.Contains (rootPhase 658) := by
  have hh := CBox.mul_contains root329_contains root329_contains (c:=root658) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def mid659 : CBox := root658
lemma mid659_contains : mid659.Contains (rootPhase 658) := root658_contains
def root659 : CBox := ⟨⟨(-620057211763289178656276352045),(-620057211763289178631502142010)⟩,⟨(-784556597155575233038360344435),(-784556597155575233013185031856)⟩⟩
lemma root659_contains : root659.Contains (rootPhase 659) := by
  have hh := CBox.mul_contains mid659_contains root1_contains (c:=root659) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def root660 : CBox := ⟨⟨(-615231590580626845494866190645),(-615231590580626845470172810128)⟩,⟨(-788346427626606262023578785771),(-788346427626606261998487248872)⟩⟩
lemma root660_contains : root660.Contains (rootPhase 660) := by
  have hh := CBox.mul_contains root330_contains root330_contains (c:=root660) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def mid661 : CBox := root660
lemma mid661_contains : mid661.Contains (rootPhase 660) := root660_contains
def root661 : CBox := ⟨⟨(-610382806276309452726374205590),(-610382806276309452701511845140)⟩,⟨(-792106577300212351796826627062),(-792106577300212351771571921304)⟩⟩
lemma root661_contains : root661.Contains (rootPhase 661) := by
  have hh := CBox.mul_contains mid661_contains root1_contains (c:=root661) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def root662 : CBox := ⟨⟨(-605511041404325513930669818371),(-605511041404325513905735797315)⟩,⟨(-795836904608883536277301646205),(-795836904608883536251970913845)⟩⟩
lemma root662_contains : root662.Contains (rootPhase 662) := by
  have hh := CBox.mul_contains root331_contains root331_contains (c:=root662) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def mid663 : CBox := root662
lemma mid663_contains : mid663.Contains (rootPhase 662) := root662_contains
def root663 : CBox := ⟨⟨(-600616479383868926663989116651),(-600616479383868926638884507400)⟩,⟨(-799537269107905033514826043536),(-799537269107905033489330859264)⟩⟩
lemma root663_contains : root663.Contains (rootPhase 663) := by
  have hh := CBox.mul_contains mid663_contains root1_contains (c:=root663) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def root664 : CBox := ⟨⟨(-595699304492433343477070366139),(-595699304492433343452094740245)⟩,⟨(-803207531480644909821180585592),(-803207531480644909795812359586)⟩⟩
lemma root664_contains : root664.Contains (rootPhase 664) := by
  have hh := CBox.mul_contains root332_contains root332_contains (c:=root664) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def mid665 : CBox := root664
lemma mid665_contains : mid665.Contains (rootPhase 664) := root664_contains
def root665 : CBox := ⟨⟨(-590759701858874228433992392324),(-590759701858874228408845806198)⟩,⟨(-806847553543799272221088269592),(-806847553543799272195555527883)⟩⟩
lemma root665_contains : root665.Contains (rootPhase 665) := by
  have hh := CBox.mul_contains mid665_contains root1_contains (c:=root665) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def root666 : CBox := ⟨⟨(-585797857456438860338205802374),(-585797857456438860312988708327)⟩,⟨(-810457198252594791741302294290),(-810457198252594791715694772637)⟩⟩
lemma root666_contains : root666.Contains (rootPhase 666) := by
  have hh := CBox.mul_contains root333_contains root333_contains (c:=root666) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def mid667 : CBox := root666
lemma mid667_contains : mid667.Contains (rootPhase 666) := root666_contains
def root667 : CBox := ⟨⟨(-580813958095764545085791804775),(-580813958095764545060402146365)⟩,⟨(-814036329705948361669185849508),(-814036329705948361643412527589)⟩⟩
lemma root667_contains : root667.Contains (rootPhase 667) := by
  have hh := CBox.mul_contains mid667_contains root1_contains (c:=root667) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def root668 : CBox := ⟨⟨(-575808191417845300756108780099),(-575808191417845300730810231161)⟩,⟨(-817584813151583696519530807421),(-817584813151583696493850531697)⟩⟩
lemma root668_contains : root668.Contains (rootPhase 668) := by
  have hh := CBox.mul_contains root334_contains root334_contains (c:=root668) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def mid669 : CBox := root668
lemma mid669_contains : mid669.Contains (rootPhase 668) := root668_contains
def root669 : CBox := ⟨⟨(-570780745886967280242861173806),(-570780745886967280217389477637)⟩,⟨(-821102514991104679075110969592),(-821102514991104679049264589467)⟩⟩
lemma root669_contains : root669.Contains (rootPhase 669) := by
  have hh := CBox.mul_contains mid669_contains root1_contains (c:=root669) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def root670 : CBox := ⟨⟨(-565731810783613197399993466852),(-565731810783613197374452425467)⟩,⟨(-824589302785025264489507761806),(-824589302785025264463587753280)⟩⟩
lemma root670_contains : root670.Contains (rootPhase 670) := by
  have hh := CBox.mul_contains root335_contains root335_contains (c:=root670) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def mid671 : CBox := root670
lemma mid671_contains : mid671.Contains (rootPhase 670) := root670_contains
def root671 : CBox := ⟨⟨(-560661576197336023850011589952),(-560661576197336023824295799355)⟩,⟨(-828045045257755752082302261577),(-828045045257755752056214861261)⟩⟩
lemma root671_contains : root671.Contains (rootPhase 671) := by
  have hh := CBox.mul_contains mid671_contains root1_contains (c:=root671) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def root672 : CBox := ⟨⟨(-555570233019602224753038437235),(-555570233019602224727481336302)⟩,⟨(-831469612302545237093472347663),(-831469612302545237067540020741)⟩⟩
lemma root672_contains : root672.Contains (rootPhase 672) := by
  have hh := CBox.mul_contains root336_contains root336_contains (c:=root672) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def mid673 : CBox := root672
lemma mid673_contains : mid673.Contains (rootPhase 672) := root672_contains
def root673 : CBox := ⟨⟨(-550457972936604802987570661366),(-550457972936604802961838602804)⟩,⟨(-834862874986380056319155724768),(-834862874986380056293056105433)⟩⟩
lemma root673_contains : root673.Contains (rootPhase 673) := by
  have hh := CBox.mul_contains mid673_contains root1_contains (c:=root673) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def root674 : CBox := ⟨⟨(-545324988422046422324287883183),(-545324988422046422298487756256)⟩,⟨(-838224705554838043201773954051),(-838224705554838043175602050043)⟩⟩
lemma root674_contains : root674.Contains (rootPhase 674) := by
  have hh := CBox.mul_contains root337_contains root337_contains (c:=root674) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def mid675 : CBox := root674
lemma mid675_contains : mid675.Contains (rootPhase 674) := root674_contains
def root675 : CBox := ⟨⟨(-540171472729892881308220092689),(-540171472729892881282243412013)⟩,⟨(-841554977436898409618347411132),(-841554977436898409592006927379)⟩⟩
lemma root675_contains : root675.Contains (rootPhase 675) := by
  have hh := CBox.mul_contains mid675_contains root1_contains (c:=root675) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def root676 : CBox := ⟨⟨(-534997619887097210673386647460),(-534997619887097210647511442988)⟩,⟨(-844853565249707073274354279604),(-844853565249707073248116214413)⟩⟩
lemma root676_contains : root676.Contains (rootPhase 676) := by
  have hh := CBox.mul_contains root338_contains root338_contains (c:=root676) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def mid677 : CBox := root676
lemma mid677_contains : mid677.Contains (rootPhase 676) := root676_contains
def root677 : CBox := ⟨⟨(-529803624686294668226438894007),(-529803624686294668200386603042)⟩,⟨(-848120344803297251293987338687),(-848120344803297251267580435287)⟩⟩
lemma root677_contains : root677.Contains (rootPhase 677) := by
  have hh := CBox.mul_contains mid677_contains root1_contains (c:=root677) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def root678 : CBox := ⟨⟨(-524589682678468906225502093761),(-524589682678468906199383001193)⟩,⟨(-851355193105265142276165797236),(-851355193105265142249687818514)⟩⟩
lemma root678_contains : root678.Contains (rootPhase 678) := by
  have hh := CBox.mul_contains root339_contains root339_contains (c:=root678) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def mid679 : CBox := root678
lemma mid679_contains : mid679.Contains (rootPhase 678) := root678_contains
def root679 : CBox := ⟨⟨(-519355990165589587372308978391),(-519355990165589587346011206136)⟩,⟨(-854557988365400520782808887459),(-854557988365400520756160781123)⟩⟩
lemma root679_contains : root679.Contains (rootPhase 679) := by
  have hh := CBox.mul_contains mid679_contains root1_contains (c:=root679) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def root680 : CBox := ⟨⟨(-514102744193221726604082390382),(-514102744193221726577937903539)⟩,⟨(-857728610000272069917127917672),(-857728610000272069890629074221)⟩⟩
lemma root680_contains : root680.Contains (rootPhase 680) := by
  have hh := CBox.mul_contains root340_contains root340_contains (c:=root680) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def mid681 : CBox := root680
lemma mid681_contains : mid681.Contains (rootPhase 680) := root680_contains
def root681 : CBox := ⟨⟨(-508830142543107036942213560806),(-508830142543107036915890143544)⟩,⟨(-860866938637767279359512693737),(-860866938637767279332843771358)⟩⟩
lemma root681_contains : root681.Contains (rootPhase 681) := by
  have hh := CBox.mul_contains mid681_contains root1_contains (c:=root681) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def root682 : CBox := ⟨⟨(-503538383725717558702350327926),(-503538383725717558675961455561)⟩,⟨(-863972856121586737933096462500),(-863972856121586737906357828617)⟩⟩
lemma root682_contains : root682.Contains (rootPhase 682) := by
  have hh := CBox.mul_contains root341_contains root341_contains (c:=root682) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def mid683 : CBox := root682
lemma mid683_contains : mid683.Contains (rootPhase 682) := root682_contains
def root683 : CBox := ⟨⟨(-498227666972781852421543751226),(-498227666972781852394974361063)⟩,⟨(-867046245515692651495216348983),(-867046245515692651468306346803)⟩⟩
lemma root683_contains : root683.Contains (rootPhase 683) := by
  have hh := CBox.mul_contains mid683_contains root1_contains (c:=root683) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def root684 : CBox := ⟨⟨(-492898192229784036883516956061),(-492898192229784036857059676541)⟩,⟨(-870086991108711418667242601920),(-870086991108711418640444682393)⟩⟩
lemma root684_contains : root684.Contains (rootPhase 684) := by
  have hh := CBox.mul_contains root342_contains root342_contains (c:=root684) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def mid685 : CBox := root684
lemma mid685_contains : mid685.Contains (rootPhase 684) := root684_contains
def root685 : CBox := ⟨⟨(-487550160148435954652052309825),(-487550160148435954625414031925)⟩,⟨(-873094978418290098651107372155),(-873094978418290098624137872846)⟩⟩
lemma root685_contains : root685.Contains (rootPhase 685) := by
  have hh := CBox.mul_contains mid685_contains root1_contains (c:=root685) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def root686 : CBox := ⟨⟨(-482183772079122748527930396843),(-482183772079122748501228036088)⟩,⟨(-876070094195406607110885193704),(-876070094195406607083847250848)⟩⟩
lemma root686_contains : root686.Contains (rootPhase 686) := by
  have hh := CBox.mul_contains root343_contains root343_contains (c:=root686) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def mid687 : CBox := root686
lemma mid687_contains : mid687.Contains (rootPhase 686) := root686_contains
def root687 : CBox := ⟨⟨(-476799230063322133352821993472),(-476799230063322133325937050664)⟩,⟨(-879012226428633477846436269371),(-879012226428633477819225456068)⟩⟩
lemma root687_contains : root687.Contains (rootPhase 687) := by
  have hh := CBox.mul_contains mid687_contains root1_contains (c:=root687) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def root688 : CBox := ⟨⟨(-471396736825997648566947891008),(-471396736825997648540243663476)⟩,⟨(-881921264348355029727766841948),(-881921264348355029700731371937)⟩⟩
lemma root688_contains : root688.Contains (rootPhase 688) := by
  have hh := CBox.mul_contains root344_contains root344_contains (c:=root688) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def mid689 : CBox := root688
lemma mid689_contains : mid689.Contains (rootPhase 688) := root688_contains
def root689 : CBox := ⟨⟨(-465976495767966177913394495055),(-465976495767966177886507587737)⟩,⟨(-884797098430937780119088340293),(-884797098430937780091880198375)⟩⟩
lemma root689_contains : root689.Contains (rootPhase 689) := by
  have hh := CBox.mul_contains mid689_contains root1_contains (c:=root689) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def root690 : CBox := ⟨⟨(-460538710958240023643838132641),(-460538710958240023616888602796)⟩,⟨(-887639620402853947775281293487),(-887639620402853947748006158230)⟩⟩
lemma root690_contains : root690.Contains (rootPhase 690) := by
  have hh := CBox.mul_contains root345_contains root345_contains (c:=root690) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def mid691 : CBox := root690
lemma mid691_contains : mid691.Contains (rootPhase 690) := root690_contains
def root691 : CBox := ⟨⟨(-455083587126343823546605026393),(-455083587126343823519471240484)⟩,⟨(-890448723244757889967321991453),(-890448723244757889939872895100)⟩⟩
lemma root691_contains : root691.Contains (rootPhase 691) := by
  have hh := CBox.mul_contains mid691_contains root1_contains (c:=root691) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def root692 : CBox := ⟨⟨(-449611329654606600056955996778),(-449611329654606600029945024069)⟩,⟨(-893224301195515320357511635370),(-893224301195515320330184366267)⟩⟩
lemma root692_contains : root692.Contains (rootPhase 692) := by
  have hh := CBox.mul_contains root346_contains root346_contains (c:=root692) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def mid693 : CBox := root692
lemma mid693_contains : mid693.Contains (rootPhase 692) := root692_contains
def root693 : CBox := ⟨⟨(-444122144570429231652810323743),(-444122144570429231625614668523)⟩,⟨(-895966249756185155929727097630),(-895966249756185155902225704225)⟩⟩
lemma root693_contains : root693.Contains (rootPhase 693) := by
  have hh := CBox.mul_contains mid693_contains root1_contains (c:=root693) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def root694 : CBox := ⟨⟨(-438616238538527637657784445935),(-438616238538527637630527644725)⟩,⟨(-898674465693953843057160855137),(-898674465693953843029593793701)⟩⟩
lemma root694_contains : root694.Contains (rootPhase 694) := by
  have hh := CBox.mul_contains root347_contains root347_contains (c:=root694) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def mid695 : CBox := root694
lemma mid695_contains : mid695.Contains (rootPhase 694) := root694_contains
def root695 : CBox := ⟨⟨(-433093818853151968495061786940),(-433093818853151968467618731429)⟩,⟨(-901348847046022014586002269993),(-901348847046022014558259794553)⟩⟩
lemma root695_contains : root695.Contains (rootPhase 695) := by
  have hh := CBox.mul_contains mid695_contains root1_contains (c:=root695) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def root696 : CBox := ⟨⟨(-427555093430282094331704288545),(-427555093430282094304439460573)⟩,⟨(-903989293123443331601354492786),(-903989293123443331573784489979)⟩⟩
lemma root696_contains : root696.Contains (rootPhase 696) := by
  have hh := CBox.mul_contains root348_contains root348_contains (c:=root696) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def mid697 : CBox := root696
lemma mid697_contains : mid697.Contains (rootPhase 696) := root696_contains
def root697 : CBox := ⟨⟨(-422000270799799685952106042130),(-422000270799799685924654839535)⟩,⟨(-906595704514915365348186560467),(-906595704514915365320441309928)⟩⟩
lemma root697_contains : root697.Contains (rootPhase 697) := by
  have hh := CBox.mul_contains mid697_contains root1_contains (c:=root697) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def root698 : CBox := ⟨⟨(-416429560097637182573434383008),(-416429560097637182545923572507)⟩,⟨(-909167983090522376579126904769),(-909167983090522376551317465150)⟩⟩
lemma root698_contains : root698.Contains (rootPhase 698) := by
  have hh := CBox.mul_contains root349_contains root349_contains (c:=root698) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def mid699 : CBox := root698
lemma mid699_contains : mid699.Contains (rootPhase 698) := root698_contains
def root699 : CBox := ⟨⟨(-410843171057903942194383770489),(-410843171057903942166685021082)⟩,⟨(-911706032005429851419711658826),(-911706032005429851391725683407)⟩⟩
lemma root699_contains : root699.Contains (rootPhase 699) := by
  have hh := CBox.mul_contains mid699_contains root1_contains (c:=root699) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def root700 : CBox := ⟨⟨(-405241314004989870919319265753),(-405241314004989870891754269148)⟩,⟨(-914209755703530654650247099759),(-914209755703530654622392946233)⟩⟩
lemma root700_contains : root700.Contains (rootPhase 700) := by
  have hh := CBox.mul_contains root350_contains root350_contains (c:=root700) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def mid701 : CBox := root700
lemma mid701_contains : mid701.Contains (rootPhase 700) := root700_contains
def root701 : CBox := ⟨⟨(-399624199845646828555036974717),(-399624199845646828527283668794)⟩,⟨(-916679059921042663131761355310),(-916679059921042663103730552333)⟩⟩
lemma root701_contains : root701.Contains (rootPhase 701) := by
  have hh := CBox.mul_contains mid701_contains root1_contains (c:=root701) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def root702 : CBox := ⟨⟨(-393992040061048108607125535828),(-393992040061048108579314203624)⟩,⟨(-919113851690057743923797180750),(-919113851690057743895703571799)⟩⟩
lemma root702_contains : root702.Contains (rootPhase 702) := by
  have hh := CBox.mul_contains root351_contains root351_contains (c:=root702) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def mid703 : CBox := root702
lemma mid703_contains : mid703.Contains (rootPhase 702) := root702_contains
def root703 : CBox := ⟨⟨(-388345046698826291636013357120),(-388345046698826291608012156591)⟩,⟨(-921514039342041943480788238258),(-921514039342041943452516692075)⟩⟩
lemma root703_contains : root703.Contains (rootPhase 703) := by
  have hh := CBox.mul_contains mid703_contains root1_contains (c:=root703) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def root704 : CBox := ⟨⟨(-382683432365089771739361580325),(-382683432365089771711573015387)⟩,⟨(-923879532511286756143455727770),(-923879532511286756115389813082)⟩⟩
lemma root704_contains : root704.Contains (rootPhase 704) := by
  have hh := CBox.mul_contains root352_contains root352_contains (c:=root704) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def mid705 : CBox := root704
lemma mid705_contains : mid705.Contains (rootPhase 704) := root704_contains
def root705 : CBox := ⟨⟨(-377007410216418256737552503450),(-377007410216418256709574148025)⟩,⟨(-926210242138311341990138064191),(-926210242138311341961894571822)⟩⟩
lemma root705_contains : root705.Contains (rootPhase 705) := by
  have hh := CBox.mul_contains mid705_contains root1_contains (c:=root705) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def root706 : CBox := ⟨⟨(-371317193951837543422936115230),(-371317193951837543394901384973)⟩,⟨(-928506080473215565952525940044),(-928506080473215565924221210924)⟩⟩
lemma root706_contains : root706.Contains (rootPhase 706) := by
  have hh := CBox.mul_contains root353_contains root353_contains (c:=root706) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def mid707 : CBox := root706
lemma mid707_contains : mid707.Contains (rootPhase 706) := root706_contains
def root707 : CBox := ⟨⟨(-365612997804773870022831100013),(-365612997804773869994605029630)⟩,⟨(-930766961078983731960303467562),(-930766961078983731931819876335)⟩⟩
lemma root707_contains : root707.Contains (rootPhase 707) := by
  have hh := CBox.mul_contains mid707_contains root1_contains (c:=root707) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def root708 : CBox := ⟨⟨(-359895036534988148786105891077),(-359895036534988148758024498984)⟩,⟨(-932992798834738887727003532266),(-932992798834738887698661753126)⟩⟩
lemma root708_contains : root708.Contains (rootPhase 708) := by
  have hh := CBox.mul_contains root354_contains root354_contains (c:=root708) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def mid709 : CBox := root708
lemma mid709_contains : mid709.Contains (rootPhase 708) := root708_contains
def root709 : CBox := ⟨⟨(-354163525420490382368481501876),(-354163525420490382340208457005)⟩,⟨(-935183509938947577657623177215),(-935183509938947577629102472983)⟩⟩
lemma root709_contains : root709.Contains (rootPhase 709) := by
  have hh := CBox.mul_contains mid709_contains root1_contains (c:=root709) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def root710 : CBox := ⟨⟨(-348418680249434568430410294047),(-348418680249434568402082558869)⟩,⟨(-937339011912574923217328051646),(-937339011912574923188747549612)⟩⟩
lemma root710_contains : root710.Contains (rootPhase 710) := by
  have hh := CBox.mul_contains root355_contains root355_contains (c:=root710) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def mid711 : CBox := root710
lemma mid711_contains : mid711.Contains (rootPhase 710) := root710_contains
def root711 : CBox := ⟨⟨(-342660717311994397603969038170),(-342660717311994397575448106633)⟩,⟨(-939459223602189911978170574476),(-939459223602189911949409864020)⟩⟩
lemma root711_contains : root711.Contains (rootPhase 711) := by
  have hh := CBox.mul_contains mid711_contains root1_contains (c:=root711) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def root712 : CBox := ⟨⟨(-336889853392220050700327336611),(-336889853392220050672009963189)⟩,⟨(-941544065183020778427895229417),(-941544065183020778399330864275)⟩⟩
lemma root712_contains : root712.Contains (rootPhase 712) := by
  have hh := CBox.mul_contains root356_contains root356_contains (c:=root712) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def mid713 : CBox := root712
lemma mid713_contains : mid713.Contains (rootPhase 712) := root712_contains
def root713 : CBox := ⟨⟨(-331106305759876401748350394919),(-331106305759876401719839843280)⟩,⟨(-943593458161960361510759808548),(-943593458161960361482015523010)⟩⟩
lemma root713_contains : root713.Contains (rootPhase 713) := by
  have hh := CBox.mul_contains mid713_contains root1_contains (c:=root713) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def root714 : CBox := ⟨⟨(-325310292162262934147129890839),(-325310292162262934118566373664)⟩,⟨(-945607325380521325746415335388),(-945607325380521325717612842417)⟩⟩
lemma root714_contains : root714.Contains (rootPhase 714) := by
  have hh := CBox.mul_contains root357_contains root357_contains (c:=root714) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def mid715 : CBox := root714
lemma mid715_contains : mid715.Contains (rootPhase 714) := root714_contains
def root715 : CBox := ⟨⟨(-319502030816015677912779951666),(-319502030816015677884021721883)⟩,⟨(-947585591017741134668930258674),(-947585591017741134639946565243)⟩⟩
lemma root715_contains : root715.Contains (rootPhase 715) := by
  have hh := CBox.mul_contains mid715_contains root1_contains (c:=root715) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def root716 : CBox := ⟨⟨(-313681740398891476667651833522),(-313681740398891476639049469587)⟩,⟨(-949528180593036667211385273385),(-949528180593036667182553646984)⟩⟩
lemma root716_contains : root716.Contains (rootPhase 716) := by
  have hh := CBox.mul_contains root358_contains root358_contains (c:=root716) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def mid717 : CBox := root716
lemma mid717_contains : mid717.Contains (rootPhase 716) := root716_contains
def root717 : CBox := ⟨⟨(-307849640041534893693323456349),(-307849640041534893664526126668)⟩,⟨(-951435020969008369564697576667),(-951435020969008369535684738732)⟩⟩
lemma root717_contains : root717.Contains (rootPhase 717) := by
  have hh := CBox.mul_contains mid717_contains root1_contains (c:=root717) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def root718 : CBox := ⟨⟨(-302005949319228067014738072348),(-302005949319228066985889565385)⟩,⟨(-953306040354193836932272857213),(-953306040354193836903203307332)⟩⟩
lemma root718_contains : root718.Contains (rootPhase 718) := by
  have hh := CBox.mul_contains root359_contains root359_contains (c:=root718) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def mid719 : CBox := root718
lemma mid719_contains : mid719.Contains (rootPhase 718) := root718_contains
def root719 : CBox := ⟨⟨(-296150888243623824133148757750),(-296150888243623824104103757494)⟩,⟨(-955141168305770721513763451047),(-955141168305770721484511411485)⟩⟩
lemma root719_contains : root719.Contains (rootPhase 719) := by
  have hh := CBox.mul_contains mid719_contains root1_contains (c:=root719) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def root720 : CBox := ⟨⟨(-290284677254462367647427756096),(-290284677254462367618616545119)⟩,⟨(-956940335732208864951272745857),(-956940335732208864922246323126)⟩⟩
lemma root720_contains : root720.Contains (rootPhase 720) := by
  have hh := CBox.mul_contains root360_contains root360_contains (c:=root720) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def mid721 : CBox := root720
lemma mid721_contains : mid721.Contains (rootPhase 720) := root720_contains
def root721 : CBox := ⟨⟨(-284407537211271843629633892571),(-284407537211271843600626382724)⟩,⟨(-958703474895871555390193505515),(-958703474895871555360985049722)⟩⟩
lemma root721_contains : root721.Contains (rootPhase 721) := by
  have hh := CBox.mul_contains mid721_contains root1_contains (c:=root721) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def root722 : CBox := ⟨⟨(-278519689385053105219186331194),(-278519689385053105190129469340)⟩,⟨(-960430519415565811214592122294),(-960430519415565811185328622093)⟩⟩
lemma root722_contains : root722.Contains (rootPhase 722) := by
  have hh := CBox.mul_contains root361_contains root361_contains (c:=root722) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def mid723 : CBox := root722
lemma mid723_contains : mid723.Contains (rootPhase 722) := root722_contains
def root723 : CBox := ⟨⟨(-272621355449948984504774146332),(-272621355449948984475519468875)⟩,⟨(-962121404269041595445234613701),(-962121404269041595415787807076)⟩⟩
lemma root723_contains : root723.Contains (rootPhase 723) := by
  have hh := CBox.mul_contains mid723_contains root1_contains (c:=root723) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def root724 : CBox := ⟨⟨(-266712757474898386336619730407),(-266712757474898386307532082672)⟩,⟨(-963776065795439866701995071865),(-963776065795439866672710569766)⟩⟩
lemma root724_contains : root724.Contains (rootPhase 724) := by
  have hh := CBox.mul_contains root362_contains root362_contains (c:=root724) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def mid725 : CBox := root724
lemma mid725_contains : mid725.Contains (rootPhase 724) := root724_contains
def root725 : CBox := ⟨⟨(-260794117915275518291608895171),(-260794117915275518262323239704)⟩,⟨(-965394441697689374566447689469),(-965394441697689374536979922741)⟩⟩
lemma root725_contains : root725.Contains (rootPhase 725) := by
  have hh := CBox.mul_contains mid725_contains root1_contains (c:=root725) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def root726 : CBox := ⟨⟨(-254865659604514571565417169559),(-254865659604514571536084051700)⟩,⟨(-966976471044852109102832201066),(-966976471044852109073310940015)⟩⟩
lemma root726_contains : root726.Contains (rootPhase 726) := by
  have hh := CBox.mul_contains root363_contains root363_contains (c:=root726) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def mid727 : CBox := root726
lemma mid727_contains : mid727.Contains (rootPhase 726) := root726_contains
def root727 : CBox := ⟨⟨(-248927605745720168122209346103),(-248927605745720168092676711404)⟩,⟨(-968522094274417316236773881099),(-968522094274417316207068084801)⟩⟩
lemma root727_contains : root727.Contains (rootPhase 727) := by
  have hh := CBox.mul_contains mid727_contains root1_contains (c:=root727) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def root728 : CBox := ⟨⟨(-242980179903263889959676559657),(-242980179903263889930373166649)⟩,⟨(-970031253194543992619540557689),(-970031253194543992590055611472)⟩⟩
lemma root728_contains : root728.Contains (rootPhase 728) := by
  have hh := CBox.mul_contains root364_contains root364_contains (c:=root728) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def mid729 : CBox := root728
lemma mid729_contains : mid729.Contains (rootPhase 728) := root728_contains
def root729 : CBox := ⟨⟨(-237023605994367206879228585676),(-237023605994367206849725839940)⟩,⟨(-971503890986251775552729170985),(-971503890986251775523060103097)⟩⟩
lemma root729_contains : root729.Contains (rootPhase 729) := by
  have hh := CBox.mul_contains mid729_contains root1_contains (c:=root729) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def root730 : CBox := ⟨⟨(-231058108280671119654742174623),(-231058108280671119625193871931)⟩,⟨(-972939952205560145483356614388),(-972939952205560145453635750077)⟩⟩
lemma root730_contains : root730.Contains (rootPhase 730) := by
  have hh := CBox.mul_contains root365_contains root365_contains (c:=root730) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def mid731 : CBox := root730
lemma mid731_contains : mid731.Contains (rootPhase 730) := root730_contains
def root731 : CBox := ⟨⟨(-225083911359792836003239518010),(-225083911359792835973490364342)⟩,⟨(-974339382785575860534431831327),(-974339382785575860504525579655)⟩⟩
lemma root731_contains : root731.Contains (rootPhase 731) := by
  have hh := CBox.mul_contains mid731_contains root1_contains (c:=root731) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def root732 : CBox := ⟨⟨(-219101240156869797239236669222),(-219101240156869797209665922764)⟩,⟨(-975702130038528544476000440906),(-975702130038528544446266937426)⟩⟩
lemma root732_contains : root732.Contains (rootPhase 732) := by
  have hh := CBox.mul_contains root366_contains root366_contains (c:=root732) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def mid733 : CBox := root732
lemma mid733_contains : mid733.Contains (rootPhase 732) := root732_contains
def root733 : CBox := ⟨⟨(-213110319916091373979348168380),(-213110319916091373949576441391)⟩,⟨(-977028142657754351501544333913),(-977028142657754351471625538900)⟩⟩
lemma root733_contains : root733.Contains (rootPhase 733) := by
  have hh := CBox.mul_contains mid733_contains root1_contains (c:=root733) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def root734 : CBox := ⟨⟨(-207111376192218549719719603849),(-207111376192218549689904310930)⟩,⟨(-978317370719627633121924035828),(-978317370719627633091955049298)⟩⟩
lemma root734_contains : root734.Contains (rootPhase 734) := by
  have hh := CBox.mul_contains root367_contains root367_contains (c:=root734) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def mid735 : CBox := root734
lemma mid735_contains : mid735.Contains (rootPhase 734) := root734_contains
def root735 : CBox := ⟨⟨(-201104634842091911570139628401),(-201104634842091911540121865109)⟩,⟨(-979569765685440534455083964405),(-979569765685440534424928424235)⟩⟩
lemma root735_contains : root735.Contains (rootPhase 735) := by
  have hh := CBox.mul_contains mid735_contains root1_contains (c:=root735) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def root736 : CBox := ⟨⟨(-195090322016128267859839359722),(-195090322016128267830087532235)⟩,⟨(-980785280403230449141792260174),(-980785280403230449111893496697)⟩⟩
lemma root736_contains : root736.Contains (rootPhase 736) := by
  have hh := CBox.mul_contains root368_contains root368_contains (c:=root736) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def mid737 : CBox := root736
lemma mid737_contains : mid737.Contains (rootPhase 736) := root736_contains
def root737 : CBox := ⟨⟨(-189068664149806212766644862684),(-189068664149806212736690947844)⟩,⟨(-981963869109555264088531620949),(-981963869109555264058446926523)⟩⟩
lemma root737_contains : root737.Contains (rootPhase 737) := by
  have hh := CBox.mul_contains mid737_contains root1_contains (c:=root737) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def root738 : CBox := ⟨⟨(-183039887955140958528191993101),(-183039887955140958498196510945)⟩,⟨(-983105487431216327195989229088),(-983105487431216327165856116108)⟩⟩
lemma root738_contains : root738.Contains (rootPhase 738) := by
  have hh := CBox.mul_contains root369_contains root369_contains (c:=root738) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def mid739 : CBox := root738
lemma mid739_contains : mid739.Contains (rootPhase 738) := root738_contains
def root739 : CBox := ⟨⟨(-177004220412148756208592761515),(-177004220412148756178393714877)⟩,⟨(-984210092386929073209636373953),(-984210092386929073179316074590)⟩⟩
lemma root739_contains : root739.Contains (rootPhase 739) := by
  have hh := CBox.mul_contains mid739_contains root1_contains (c:=root739) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def root740 : CBox := ⟨⟨(-170961888760301226375292277232),(-170961888760301226345282899166)⟩,⟨(-985277642388941244789669120233),(-985277642388941244759531901934)⟩⟩
lemma root740_contains : root740.Contains (rootPhase 740) := by
  have hh := CBox.mul_contains root370_contains root370_contains (c:=root740) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def mid741 : CBox := root740
lemma mid741_contains : mid741.Contains (rootPhase 740) := root740_contains
def root741 : CBox := ⟨⟨(-164913120489969921429932801830),(-164913120489969921399719793474)⟩,⟨(-986308097244598647879021892618),(-986308097244598647848697638498)⟩⟩
lemma root741_contains : root741.Contains (rootPhase 741) := by
  have hh := CBox.mul_contains mid741_contains root1_contains (c:=root741) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def root742 : CBox := ⟨⟨(-158858143333861441696140857991),(-158858143333861441665888371397)⟩,⟨(-987301418157858382415543637350),(-987301418157858382385172621738)⟩⟩
lemma root742_contains : root742.Contains (rootPhase 742) := by
  have hh := CBox.mul_contains root371_contains root371_contains (c:=root742) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def mid743 : CBox := root742
lemma mid743_contains : mid743.Contains (rootPhase 742) := root742_contains
def root743 : CBox := ⟨⟨(-152797185258443427732186848613),(-152797185258443427701729263778)⟩,⟨(-988257567730749491420594527575),(-988257567730749491390035225127)⟩⟩
lemma root743_contains : root743.Contains (rootPhase 743) := by
  have hh := CBox.mul_contains mid743_contains root1_contains (c:=root743) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def root744 : CBox := ⟨⟨(-146730474455361751670565184024),(-146730474455361751640362576943)⟩,⟨(-989176509964780973467332812144),(-989176509964780973437019209558)⟩⟩
lemma root744_contains : root744.Contains (rootPhase 744) := by
  have hh := CBox.mul_contains root372_contains root372_contains (c:=root744) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def mid745 : CBox := root744
lemma mid745_contains : mid745.Contains (rootPhase 744) := root744_contains
def root745 : CBox := ⟨⟨(-140658239332849230726598718158),(-140658239332849230696191329110)⟩,⟨(-990058210262297105521639271213),(-990058210262297105491137923523)⟩⟩
lemma root745_contains : root745.Contains (rootPhase 745) := by
  have hh := CBox.mul_contains mid745_contains root1_contains (c:=root745) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def root746 : CBox := ⟨⟨(-134580708507126186328179527695),(-134580708507126186297734737715)⟩,⟨(-990902635427780025123972084192),(-990902635427780025093425774696)⟩⟩
lemma root746_contains : root746.Contains (rootPhase 746) := by
  have hh := CBox.mul_contains root373_contains root373_contains (c:=root746) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def mid747 : CBox := root746
lemma mid747_contains : mid747.Contains (rootPhase 746) := root746_contains
def root747 : CBox := ⟨⟨(-128498110793793172636332493007),(-128498110793793172605681465603)⟩,⟨(-991709753669099522875859212196),(-991709753669099522845123913178)⟩⟩
lemma root747_contains : root747.Contains (rootPhase 747) := by
  have hh := CBox.mul_contains mid747_contains root1_contains (c:=root747) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def root748 : CBox := ⟨⟨(-122410675199216198510513580563),(-122410675199216198480063723516)⟩,⟨(-992479534598709998172459355143),(-992479534598709998141917691448)⟩⟩
lemma root748_contains : root748.Contains (rootPhase 748) := by
  have hh := CBox.mul_contains root374_contains root374_contains (c:=root748) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def mid749 : CBox := root748
lemma mid749_contains : mid749.Contains (rootPhase 748) := root748_contains
def root749 : CBox := ⟨⟨(-116318630911904767264449454362),(-116318630911904767233793359258)⟩,⟨(-993211949234794533120367075258),(-993211949234794533089636628488)⟩⟩
lemma root749_contains : root749.Contains (rootPhase 749) := by
  have hh := CBox.mul_contains mid749_contains root1_contains (c:=root749) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def root750 : CBox := ⟨⟨(-110222207293883058819814913732),(-110222207293883058789123604886)⟩,⟨(-993906970002356041562689999449),(-993906970002356041531916300553)⟩⟩
lemma root750_contains : root750.Contains (rootPhase 750) := by
  have hh := CBox.mul_contains root375_contains root375_contains (c:=root750) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def mid751 : CBox := root750
lemma mid751_contains : mid751.Contains (rootPhase 750) := root750_contains
def root751 : CBox := ⟨⟨(-104121633872054579132956650022),(-104121633872054579102057657613)⟩,⟨(-994564570734255452134947867235),(-994564570734255452103984146115)⟩⟩
lemma root751_contains : root751.Contains (rootPhase 751) := by
  have hh := CBox.mul_contains mid751_contains root1_contains (c:=root751) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def root752 : CBox := ⟨⟨(-98017140329560602006057786733),(-98017140329560601975446444917)⟩,⟨(-995184726672196886260518981772),(-995184726672196886229833164667)⟩⟩
lemma root752_contains : root752.Contains (rootPhase 752) := by
  have hh := CBox.mul_contains root376_contains root376_contains (c:=root752) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def mid753 : CBox := root752
lemma mid753_contains : mid753.Contains (rootPhase 752) := root752_contains
def root753 : CBox := ⟨⟨(-91908956497132728636950188818),(-91908956497132728606131677782)⟩,⟨(-995767414467659793998251606478),(-995767414467659793967376494511)⟩⟩
lemma root753_contains : root753.Contains (rootPhase 753) := by
  have hh := CBox.mul_contains mid753_contains root1_contains (c:=root753) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def root754 : CBox := ⟨⟨(-85797312344439890473525596765),(-85797312344439890442674029951)⟩,⟨(-996312612182778012642982067958),(-996312612182778012612065566649)⟩⟩
lemma root754_contains : root754.Contains (rootPhase 754) := by
  have hh := CBox.mul_contains root377_contains root377_contains (c:=root754) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def mid755 : CBox := root754
lemma mid755_contains : mid755.Contains (rootPhase 754) := root754_contains
def root755 : CBox := ⟨⟨(-79682437971430121159187873196),(-79682437971430121128127705780)⟩,⟨(-996820299291165714988459691753),(-996820299291165714957352664587)⟩⟩
lemma root755_contains : root755.Contains (rootPhase 755) := by
  have hh := CBox.mul_contains mid755_contains root1_contains (c:=root755) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def root756 : CBox := ⟨⟨(-73564563599667423541420345354),(-73564563599667423510572721098)⟩,⟨(-997290456678690216151304488072),(-997290456678690216120401522919)⟩⟩
lemma root756_contains : root756.Contains (rootPhase 756) := by
  have hh := CBox.mul_contains root378_contains root378_contains (c:=root756) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def mid757 : CBox := root756
lemma mid757_contains : mid757.Contains (rootPhase 756) := root756_contains
def root757 : CBox := ⟨⟨(-67443919563664057910025317835),(-67443919563664057878969158441)⟩,⟨(-997723066644191609864328227356),(-997723066644191609833234999210)⟩⟩
lemma root757_contains : root757.Contains (rootPhase 757) := by
  have hh := CBox.mul_contains mid757_contains root1_contains (c:=root757) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def root758 : CBox := ⟨⟨(-61320736302208577794676907539),(-61320736302208577763589974110)⟩,⟨(-998118112900149207140936128818),(-998118112900149207109803270980)⟩⟩
lemma root758_contains : root758.Contains (rootPhase 758) := by
  have hh := CBox.mul_contains root379_contains root379_contains (c:=root758) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def mid759 : CBox := root758
lemma mid759_contains : mid759.Contains (rootPhase 758) := root758_contains
def root759 : CBox := ⟨⟨(-55195244349689939821608977470),(-55195244349689939790312088231)⟩,⟨(-998475580573294752224413940450),(-998475580573294752193089594737)⟩⟩
lemma root759_contains : root759.Contains (rootPhase 759) := by
  have hh := CBox.mul_contains mid759_contains root1_contains (c:=root759) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def root760 : CBox := ⟨⟨(-49067674327418014266970358521),(-49067674327418014235954184491)⟩,⟨(-998795456205172392730469908535),(-998795456205172392699416411952)⟩⟩
lemma root760_contains : root760.Contains (rootPhase 760) := by
  have hh := CBox.mul_contains root380_contains root380_contains (c:=root760) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def mid761 : CBox := root760
lemma mid761_contains : mid761.Contains (rootPhase 760) := root760_contains
def root761 : CBox := ⟨⟨(-42938256934940823089239078919),(-42938256934940823058013423054)⟩,⟨(-999077727752645382904554472018),(-999077727752645382873310159601)⟩⟩
lemma root761_contains : root761.Contains (rootPhase 761) := by
  have hh := CBox.mul_contains mid761_contains root1_contains (c:=root761) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def root762 : CBox := ⟨⟨(-36807222941358832336456042395),(-36807222941358832305201851719)⟩,⟨(-999322384588349500911991054777),(-999322384588349500880709008171)⟩⟩
lemma root762_contains : root762.Contains (rootPhase 762) := by
  have hh := CBox.mul_contains root381_contains root381_contains (c:=root762) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def mid763 : CBox := root762
lemma mid763_contains : mid763.Contains (rootPhase 762) := root762_contains
def root763 : CBox := ⟨⟨(-30674803176636625946244498501),(-30674803176636625914779419411)⟩,⟨(-999529417501093163095548022122),(-999529417501093163064073943069)⟩⟩
lemma root763_contains : root763.Contains (rootPhase 763) := by
  have hh := CBox.mul_contains mid763_contains root1_contains (c:=root763) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def root764 : CBox := ⟨⟨(-24541228522912288043840754563),(-24541228522912288012599778426)⟩,⟨(-999698818696204220131481605168),(-999698818696204220100222174267)⟩⟩
lemma root764_contains : root764.Contains (rootPhase 764) := by
  have hh := CBox.mul_contains root382_contains root382_contains (c:=root764) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def mid765 : CBox := root764
lemma mid765_contains : mid765.Contains (rootPhase 764) := root764_contains
def root765 : CBox := ⟨⟨(-18406729905804820939572852517),(-18406729905804820908121120722)⟩,⟨(-999830581795823422031512606410),(-999830581795823422000061463374)⟩⟩
lemma root765_contains : root765.Contains (rootPhase 765) := by
  have hh := CBox.mul_contains mid765_contains root1_contains (c:=root765) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def root766 : CBox := ⟨⟨(-12271538285719926091622949095),(-12271538285719926060145058079)⟩,⟨(-999924701839144540937433246002),(-999924701839144540905946178377)⟩⟩
lemma root766_contains : root766.Contains (rootPhase 766) := by
  have hh := CBox.mul_contains root383_contains root383_contains (c:=root766) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def mid767 : CBox := root766
lemma mid767_contains : mid767.Contains (rootPhase 766) := root766_contains
def root767 : CBox := ⟨⟨(-6135884649154475371956197144),(-6135884649154475340266155359)⟩,⟨(-999981175282601142672852056363),(-999981175282601142641172066954)⟩⟩
lemma root767_contains : root767.Contains (rootPhase 767) := by
  have hh := CBox.mul_contains mid767_contains root1_contains (c:=root767) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def root768 : CBox := ⟨⟨(-12150246369),19217697693⟩,⟨(-1000000000000000000015683941643),(-999999999999999999984315997582)⟩⟩
lemma root768_contains : root768.Contains (rootPhase 768) := by
  have hh := CBox.mul_contains root384_contains root384_contains (c:=root768) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def mid769 : CBox := root768
lemma mid769_contains : mid769.Contains (rootPhase 768) := root768_contains
def root769 : CBox := ⟨⟨6135884649154475347388811739,6135884649154475378968177588⟩,⟨(-999981175282601142672748673368),(-999981175282601142641188719705)⟩⟩
lemma root769_contains : root769.Contains (rootPhase 769) := by
  have hh := CBox.mul_contains mid769_contains root1_contains (c:=root769) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def root770 : CBox := ⟨⟨12271538285719926067149313160,12271538285719926098752532589⟩,⟨(-999924701839144540937399947052),(-999924701839144540905806020058)⟩⟩
lemma root770_contains : root770.Contains (rootPhase 770) := by
  have hh := CBox.mul_contains root385_contains root385_contains (c:=root770) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def mid771 : CBox := root770
lemma mid771_contains : mid771.Contains (rootPhase 770) := root770_contains
def root771 : CBox := ⟨⟨18406729905804820915005228958,18406729905804820946821252474⟩,⟨(-999830581795823422031550753892),(-999830581795823421999763138125)⟩⟩
lemma root771_contains : root771.Contains (rootPhase 771) := by
  have hh := CBox.mul_contains mid771_contains root1_contains (c:=root771) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def root772 : CBox := ⟨⟨24541228522912288019495282976,24541228522912288051075895743⟩,⟨(-999698818696204220131459522397),(-999698818696204220099897368566)⟩⟩
lemma root772_contains : root772.Contains (rootPhase 772) := by
  have hh := CBox.mul_contains root386_contains root386_contains (c:=root772) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def mid773 : CBox := root772
lemma mid773_contains : mid773.Contains (rootPhase 772) := root772_contains
def root773 : CBox := ⟨⟨30674803176636625921679474830,30674803176636625953472694334⟩,⟨(-999529417501093163095472161658),(-999529417501093163063716217420)⟩⟩
lemma root773_contains : root773.Contains (rootPhase 773) := by
  have hh := CBox.mul_contains mid773_contains root1_contains (c:=root773) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def root774 : CBox := ⟨⟨36807222941358832311984308478,36807222941358832343798910486⟩,⟨(-999322384588349500911983448969),(-999322384588349500880196346549)⟩⟩
lemma root774_contains : root774.Contains (rootPhase 774) := by
  have hh := CBox.mul_contains root387_contains root387_contains (c:=root774) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def mid775 : CBox := root774
lemma mid775_contains : mid775.Contains (rootPhase 774) := root774_contains
def root775 : CBox := ⟨⟨42938256934940823064672894885,42938256934940823096701473722⟩,⟨(-999077727752645382904620133220),(-999077727752645382872637569241)⟩⟩
lemma root775_contains : root775.Contains (rootPhase 775) := by
  have hh := CBox.mul_contains mid775_contains root1_contains (c:=root775) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def root776 : CBox := ⟨⟨49067674327418014242659971234,49067674327418014274382448514⟩,⟨(-998795456205172392730438962364),(-998795456205172392698753790087)⟩⟩
lemma root776_contains : root776.Contains (rootPhase 776) := by
  have hh := CBox.mul_contains root388_contains root388_contains (c:=root776) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def mid777 : CBox := root776
lemma mid777_contains : mid777.Contains (rootPhase 776) := root776_contains
def root777 : CBox := ⟨⟨55195244349689939797049299649,55195244349689939828985121357⟩,⟨(-998475580573294752224301832201),(-998475580573294752192421522186)⟩⟩
lemma root777_contains : root777.Contains (rootPhase 777) := by
  have hh := CBox.mul_contains mid777_contains root1_contains (c:=root777) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def root778 : CBox := ⟨⟨61320736302208577770210187351,61320736302208577802164996812⟩,⟨(-998118112900149207140890580942),(-998118112900149207108982054663)⟩⟩
lemma root778_contains : root778.Contains (rootPhase 778) := by
  have hh := CBox.mul_contains root389_contains root389_contains (c:=root778) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def mid779 : CBox := root778
lemma mid779_contains : mid779.Contains (rootPhase 778) := root778_contains
def root779 : CBox := ⟨⟨67443919563664057885463843241,67443919563664057917633351588⟩,⟨(-997723066644191609864357618177),(-997723066644191609832252293437)⟩⟩
lemma root779_contains : root779.Contains (rootPhase 779) := by
  have hh := CBox.mul_contains mid779_contains root1_contains (c:=root779) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def root780 : CBox := ⟨⟨73564563599667423517083564801,73564563599667423549006105284⟩,⟨(-997290456678690216151266796707),(-997290456678690216119399384468)⟩⟩
lemma root780_contains : root780.Contains (rootPhase 780) := by
  have hh := CBox.mul_contains root390_contains root390_contains (c:=root780) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def mid781 : CBox := root780
lemma mid781_contains : mid781.Contains (rootPhase 780) := root780_contains
def root781 : CBox := ⟨⟨79682437971430121134634281918,79682437971430121166771255041⟩,⟨(-996820299291165714988375151723),(-996820299291165714956310899085)⟩⟩
lemma root781_contains : root781.Contains (rootPhase 781) := by
  have hh := CBox.mul_contains mid781_contains root1_contains (c:=root781) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def root782 : CBox := ⟨⟨85797312344439890449064503687,85797312344439890481217904878⟩,⟨(-996312612182778012642962252225),(-996312612182778012610872643537)⟩⟩
lemma root782_contains : root782.Contains (rootPhase 782) := by
  have hh := CBox.mul_contains root391_contains root391_contains (c:=root782) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def mid783 : CBox := root782
lemma mid783_contains : mid783.Contains (rootPhase 782) := root782_contains
def root783 : CBox := ⟨⟨91908956497132728612393883383,91908956497132728644763058721⟩,⟨(-995767414467659793998308537430),(-995767414467659793966020437063)⟩⟩
lemma root783_contains : root783.Contains (rootPhase 783) := by
  have hh := CBox.mul_contains mid783_contains root1_contains (c:=root783) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def root784 : CBox := ⟨⟨98017140329560601981771319072,98017140329560602013799751827⟩,⟨(-995184726672196886260460364185),(-995184726672196886228506317015)⟩⟩
lemma root784_contains : root784.Contains (rootPhase 784) := by
  have hh := CBox.mul_contains root392_contains root392_contains (c:=root784) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def mid785 : CBox := root784
lemma mid785_contains : mid785.Contains (rootPhase 784) := root784_contains
def root785 : CBox := ⟨⟨104121633872054579108414512001,104121633872054579140657869013⟩,⟨(-994564570734255452134806137393),(-994564570734255452102654124128)⟩⟩
lemma root785_contains : root785.Contains (rootPhase 785) := by
  have hh := CBox.mul_contains mid785_contains root1_contains (c:=root785) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def root786 : CBox := ⟨⟨110222207293883058795364980446,110222207293883058827622316394⟩,⟨(-993906970002356041562611351694),(-993906970002356041530436965311)⟩⟩
lemma root786_contains : root786.Contains (rootPhase 786) := by
  have hh := CBox.mul_contains root393_contains root393_contains (c:=root786) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def mid787 : CBox := root786
lemma mid787_contains : mid787.Contains (rootPhase 786) := root786_contains
def root787 : CBox := ⟨⟨116318630911904767239904091633,116318630911904767272377676121⟩,⟨(-993211949234794533120366769720),(-993211949234794533087992778519)⟩⟩
lemma root787_contains : root787.Contains (rootPhase 787) := by
  have hh := CBox.mul_contains mid787_contains root1_contains (c:=root787) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def root788 : CBox := ⟨⟨122410675199216198486195300240,122410675199216198518410605327⟩,⟨(-992479534598709998172385330906),(-992479534598709998140261449571)⟩⟩
lemma root788_contains : root788.Contains (rootPhase 788) := by
  have hh := CBox.mul_contains root394_contains root394_contains (c:=root788) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def mid789 : CBox := root788
lemma mid789_contains : mid789.Contains (rootPhase 788) := root788_contains
def root789 : CBox := ⟨⟨128498110793793172611800230531,128498110793793172644231448745⟩,⟨(-991709753669099522875745140503),(-991709753669099522843421673292)⟩⟩
lemma root789_contains : root789.Contains (rootPhase 789) := by
  have hh := CBox.mul_contains mid789_contains root1_contains (c:=root789) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def root790 : CBox := ⟨⟨134580708507126186303739011951,134580708507126186336181565544⟩,⟨(-990902635427780025123919255476),(-990902635427780025091576314750)⟩⟩
lemma root790_contains : root790.Contains (rootPhase 790) := by
  have hh := CBox.mul_contains root395_contains root395_contains (c:=root790) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def mid791 : CBox := root790
lemma mid791_contains : mid791.Contains (rootPhase 790) := root790_contains
def root791 : CBox := ⟨⟨140658239332849230702062323055,140658239332849230734722100387⟩,⟨(-990058210262297105521666577543),(-990058210262297105489122423070)⟩⟩
lemma root791_contains : root791.Contains (rootPhase 791) := by
  have hh := CBox.mul_contains mid791_contains root1_contains (c:=root791) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def root792 : CBox := ⟨⟨146730474455361751646290526993,146730474455361751678619147352⟩,⟨(-989176509964780973467247930213),(-989176509964780973435030066753)⟩⟩
lemma root792_contains : root792.Contains (rootPhase 792) := by
  have hh := CBox.mul_contains root396_contains root396_contains (c:=root792) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def mid793 : CBox := root792
lemma mid793_contains : mid793.Contains (rootPhase 792) := root792_contains
def root793 : CBox := ⟨⟨152797185258443427707669994967,152797185258443427740215041597⟩,⟨(-988257567730749491420444296569),(-988257567730749491388025678880)⟩⟩
lemma root793_contains : root793.Contains (rootPhase 793) := by
  have hh := CBox.mul_contains mid793_contains root1_contains (c:=root793) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def root794 : CBox := ⟨⟨158858143333861441671715393396,158858143333861441704269245034⟩,⟨(-987301418157858382415452943992),(-987301418157858382383017866636)⟩⟩
lemma root794_contains : root794.Contains (rootPhase 794) := by
  have hh := CBox.mul_contains root397_contains root397_contains (c:=root794) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def mid795 : CBox := root794
lemma mid795_contains : mid795.Contains (rootPhase 794) := root794_contains
def root795 : CBox := ⟨⟨164913120489969921405411196199,164913120489969921438182767601⟩,⟨(-986308097244598647879012971118),(-986308097244598647846375524871)⟩⟩
lemma root795_contains : root795.Contains (rootPhase 795) := by
  have hh := CBox.mul_contains mid795_contains root1_contains (c:=root795) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def root796 : CBox := ⟨⟨170961888760301226351000078426,170961888760301226383501901038⟩,⟨(-985277642388941244789579762786),(-985277642388941244757204725353)⟩⟩
lemma root796_contains : root796.Contains (rootPhase 796) := by
  have hh := CBox.mul_contains root398_contains root398_contains (c:=root796) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def mid797 : CBox := root796
lemma mid797_contains : mid797.Contains (rootPhase 796) := root796_contains
def root797 : CBox := ⟨⟨177004220412148756184089526352,177004220412148756216808663334⟩,⟨(-984210092386929073209513915534),(-984210092386929073176936591054)⟩⟩
lemma root797_contains : root797.Contains (rootPhase 797) := by
  have hh := CBox.mul_contains mid797_contains root1_contains (c:=root797) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def root798 : CBox := ⟨⟨183039887955140958503779693892,183039887955140958536504909907⟩,⟨(-983105487431216327195924468606),(-983105487431216327163333620910)⟩⟩
lemma root798_contains : root798.Contains (rootPhase 798) := by
  have hh := CBox.mul_contains root399_contains root399_contains (c:=root798) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def mid799 : CBox := root798
lemma mid799_contains : mid799.Contains (rootPhase 798) := root798_contains
def root799 : CBox := ⟨⟨189068664149806212742135982035,189068664149806212775079791523⟩,⟨(-981963869109555264088550406311),(-981963869109555264055755669166)⟩⟩
lemma root799_contains : root799.Contains (rootPhase 799) := by
  have hh := CBox.mul_contains mid799_contains root1_contains (c:=root799) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def root800 : CBox := ⟨⟨195090322016128267835609768708,195090322016128267868180426979⟩,⟨(-980785280403230449141676123456),(-980785280403230449109252045722)⟩⟩
lemma root800_contains : root800.Contains (rootPhase 800) := by
  have hh := CBox.mul_contains root400_contains root400_contains (c:=root800) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def mid801 : CBox := root800
lemma mid801_contains : mid801.Contains (rootPhase 800) := root800_contains
def root801 : CBox := ⟨⟨201104634842091911545659714187,201104634842091911578447901784⟩,⟨(-979569765685440534454898523122),(-979569765685440534422271265958)⟩⟩
lemma root801_contains : root801.Contains (rootPhase 801) := by
  have hh := CBox.mul_contains mid801_contains root1_contains (c:=root801) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def root802 : CBox := ⟨⟨207111376192218549695330315837,207111376192218549728122018857⟩,⟨(-978317370719627633121794662494),(-978317370719627633089156918220)⟩⟩
lemma root802_contains : root802.Contains (rootPhase 802) := by
  have hh := CBox.mul_contains root401_contains root401_contains (c:=root802) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def mid803 : CBox := root802
lemma mid803_contains : mid803.Contains (rootPhase 802) := root802_contains
def root803 : CBox := ⟨⟨213110319916091373954862156978,213110319916091373987872649530⟩,⟨(-977028142657754351501500042175),(-977028142657754351468657531591)⟩⟩
lemma root803_contains : root803.Contains (rootPhase 803) := by
  have hh := CBox.mul_contains mid803_contains root1_contains (c:=root803) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def root804 : CBox := ⟨⟨219101240156869797214982198696,219101240156869797247711846903⟩,⟨(-975702130038528544475869294207),(-975702130038528544443301103853)⟩⟩
lemma root804_contains : root804.Contains (rootPhase 804) := by
  have hh := CBox.mul_contains root402_contains root402_contains (c:=root804) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def mid805 : CBox := root804
lemma mid805_contains : mid805.Contains (rootPhase 804) := root804_contains
def root805 : CBox := ⟨⟨225083911359792835978777055505,225083911359792836011725018089⟩,⟨(-974339382785575860534274338634),(-974339382785575860501501527453)⟩⟩
lemma root805_contains : root805.Contains (rootPhase 805) := by
  have hh := CBox.mul_contains mid805_contains root1_contains (c:=root805) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def root806 : CBox := ⟨⟨231058108280671119630369890743,231058108280671119663318566164⟩,⟨(-972939952205560145483253353117),(-972939952205560145450473021615)⟩⟩
lemma root806_contains : root806.Contains (rootPhase 806) := by
  have hh := CBox.mul_contains root403_contains root403_contains (c:=root806) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def mid807 : CBox := root806
lemma mid807_contains : mid807.Contains (rootPhase 806) := root806_contains
def root807 : CBox := ⟨⟨237023605994367206854759151194,237023605994367206887927386118⟩,⟨(-971503890986251775552712744018),(-971503890986251775519726218453)⟩⟩
lemma root807_contains : root807.Contains (rootPhase 807) := by
  have hh := CBox.mul_contains mid807_contains root1_contains (c:=root807) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def root808 : CBox := ⟨⟨242980179903263889935474123063,242980179903263889968286899273⟩,⟨(-970031253194543992619396730526),(-970031253194543992586764931285)⟩⟩
lemma root808_contains : root808.Contains (rootPhase 808) := by
  have hh := CBox.mul_contains root404_contains root404_contains (c:=root808) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def mid809 : CBox := root808
lemma mid809_contains : mid809.Contains (rootPhase 808) := root808_contains
def root809 : CBox := ⟨⟨248927605745720168097772325020,248927605745720168130803696622⟩,⟨(-968522094274417316236580393483),(-968522094274417316203742998639)⟩⟩
lemma root809_contains : root809.Contains (rootPhase 809) := by
  have hh := CBox.mul_contains mid809_contains root1_contains (c:=root809) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def root810 : CBox := ⟨⟨254865659604514571541069951678,254865659604514571574099386405⟩,⟨(-966976471044852109102691240909),(-966976471044852109069849392435)⟩⟩
lemma root810_contains : root810.Contains (rootPhase 810) := by
  have hh := CBox.mul_contains root405_contains root405_contains (c:=root810) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def mid811 : CBox := root810
lemma mid811_contains : mid811.Contains (rootPhase 810) := root810_contains
def root811 : CBox := ⟨⟨260794117915275518267164316530,260794117915275518300413573257⟩,⟨(-965394441697689374566395153766),(-965394441697689374533346152381)⟩⟩
lemma root811_contains : root811.Contains (rootPhase 811) := by
  have hh := CBox.mul_contains mid811_contains root1_contains (c:=root811) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def root812 : CBox := ⟨⟨266712757474898386312408791508,266712757474898386345365900811⟩,⟨(-963776065795439866701849157861),(-963776065795439866669086518173)⟩⟩
lemma root812_contains : root812.Contains (rootPhase 812) := by
  have hh := CBox.mul_contains root406_contains root406_contains (c:=root812) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def mid813 : CBox := root812
lemma mid813_contains : mid813.Contains (rootPhase 812) := root812_contains
def root813 : CBox := ⟨⟨272621355449948984480358360119,272621355449948984513534745764⟩,⟨(-962121404269041595445069259496),(-962121404269041595412099678083)⟩⟩
lemma root813_contains : root813.Contains (rootPhase 813) := by
  have hh := CBox.mul_contains mid813_contains root1_contains (c:=root813) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def root814 : CBox := ⟨⟨278519689385053105194859909884,278519689385053105228031480748⟩,⟨(-960430519415565811214477464352),(-960430519415565811181506424321)⟩⟩
lemma root814_contains : root814.Contains (rootPhase 814) := by
  have hh := CBox.mul_contains root407_contains root407_contains (c:=root814) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def mid815 : CBox := root814
lemma mid815_contains : mid815.Contains (rootPhase 814) := root814_contains
def root815 : CBox := ⟨⟨284407537211271843605209697827,284407537211271843638601755872⟩,⟨(-958703474895871555390168999635),(-958703474895871555356989475593)⟩⟩
lemma root815_contains : root815.Contains (rootPhase 815) := by
  have hh := CBox.mul_contains mid815_contains root1_contains (c:=root815) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def root816 : CBox := ⟨⟨290284677254462367623284984685,290284677254462367656285573038⟩,⟨(-956940335732208864951101038267),(-956940335732208864918314877753)⟩⟩
lemma root816_contains : root816.Contains (rootPhase 816) := by
  have hh := CBox.mul_contains root408_contains root408_contains (c:=root816) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def mid817 : CBox := root816
lemma mid817_contains : mid817.Contains (rootPhase 816) := root816_contains
def root817 : CBox := ⟨⟨296150888243623824108766731463,296150888243623824141986609141⟩,⟨(-955141168305770721513541309723),(-955141168305770721480547481387)⟩⟩
lemma root817_contains : root817.Contains (rootPhase 817) := by
  have hh := CBox.mul_contains mid817_contains root1_contains (c:=root817) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def root818 : CBox := ⟨⟨302005949319228066990445066251,302005949319228067023657457393⟩,⟨(-953306040354193836932099772521),(-953306040354193836899107559748)⟩⟩
lemma root818_contains : root818.Contains (rootPhase 818) := by
  have hh := CBox.mul_contains root409_contains root409_contains (c:=root818) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def mid819 : CBox := root818
lemma mid819_contains : mid819.Contains (rootPhase 818) := root818_contains
def root819 : CBox := ⟨⟨307849640041534893668932575432,307849640041534893702365446725⟩,⟨(-951435020969008369564616143943),(-951435020969008369531414739043)⟩⟩
lemma root819_contains : root819.Contains (rootPhase 819) := by
  have hh := CBox.mul_contains mid819_contains root1_contains (c:=root819) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def root820 : CBox := ⟨⟨313681740398891476643496498854,313681740398891476676626290294⟩,⟨(-949528180593036667211204225784),(-949528180593036667178300825867)⟩⟩
lemma root820_contains : root820.Contains (rootPhase 820) := by
  have hh := CBox.mul_contains root410_contains root410_contains (c:=root820) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def mid821 : CBox := root820
lemma mid821_contains : mid821.Contains (rootPhase 820) := root820_contains
def root821 : CBox := ⟨⟨319502030816015677888423022641,319502030816015677921772678532⟩,⟨(-947585591017741134668736500198),(-947585591017741134635624185624)⟩⟩
lemma root821_contains : root821.Contains (rootPhase 821) := by
  have hh := CBox.mul_contains mid821_contains root1_contains (c:=root821) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def root822 : CBox := ⟨⟨325310292162262934122861553747,325310292162262934156200775687⟩,⟨(-945607325380521325746268811218),(-945607325380521325713161129147)⟩⟩
lemma root822_contains : root822.Contains (rootPhase 822) := by
  have hh := CBox.mul_contains root411_contains root411_contains (c:=root822) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def mid823 : CBox := root822
lemma mid823_contains : mid823.Contains (rootPhase 822) := root822_contains
def root823 : CBox := ⟨⟨331106305759876401723983788210,331106305759876401757544049000⟩,⟨(-943593458161960361510706636279),(-943593458161960361477388531617)⟩⟩
lemma root823_contains : root823.Contains (rootPhase 823) := by
  have hh := CBox.mul_contains mid823_contains root1_contains (c:=root823) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def root824 : CBox := ⟨⟨336889853392220050676232333237,336889853392220050709413597499⟩,⟨(-941544065183020778427699812424),(-941544065183020778394764367585)⟩⟩
lemma root824_contains : root824.Contains (rootPhase 824) := by
  have hh := CBox.mul_contains root412_contains root412_contains (c:=root824) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def mid825 : CBox := root824
lemma mid825_contains : mid825.Contains (rootPhase 824) := root824_contains
def root825 : CBox := ⟨⟨342660717311994397579647567620,342660717311994397613048738978⟩,⟨(-939459223602189911977941040651),(-939459223602189911944795913428)⟩⟩
lemma root825_contains : root825.Contains (rootPhase 825) := by
  have hh := CBox.mul_contains mid825_contains root1_contains (c:=root825) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def root826 : CBox := ⟨⟨348418680249434568406177030153,348418680249434568439565015465⟩,⟨(-937339011912574923217144061234),(-937339011912574923184006667233)⟩⟩
lemma root826_contains : root826.Contains (rootPhase 826) := by
  have hh := CBox.mul_contains root413_contains root413_contains (c:=root826) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def mid827 : CBox := root826
lemma mid827_contains : mid827.Contains (rootPhase 826) := root826_contains
def root827 : CBox := ⟨⟨354163525420490382344149818343,354163525420490382377758865320⟩,⟨(-935183509938947577657534070101),(-935183509938947577624185504349)⟩⟩
lemma root827_contains : root827.Contains (rootPhase 827) := by
  have hh := CBox.mul_contains mid827_contains root1_contains (c:=root827) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def root828 : CBox := ⟨⟨359895036534988148762011620805,359895036534988148795306528438⟩,⟨(-932992798834738887726808537603),(-932992798834738887693769657560)⟩⟩
lemma root828_contains : root828.Contains (rootPhase 828) := by
  have hh := CBox.mul_contains root414_contains root414_contains (c:=root828) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def mid829 : CBox := root828
lemma mid829_contains : mid829.Contains (rootPhase 828) := root828_contains
def root829 : CBox := ⟨⟨365612997804773869998538571789,365612997804773870032053854926⟩,⟨(-930766961078983731960102568479),(-930766961078983731926852862237)⟩⟩
lemma root829_contains : root829.Contains (rootPhase 829) := by
  have hh := CBox.mul_contains mid829_contains root1_contains (c:=root829) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def root830 : CBox := ⟨⟨371317193951837543398731378765,371317193951837543432230461070⟩,⟨(-928506080473215565952368773113),(-928506080473215565919129836291)⟩⟩
lemma root830_contains : root830.Contains (rootPhase 830) := by
  have hh := CBox.mul_contains root415_contains root415_contains (c:=root830) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def mid831 : CBox := root830
lemma mid831_contains : mid831.Contains (rootPhase 830) := root830_contains
def root831 : CBox := ⟨⟨377007410216418256713248972122,377007410216418256746969567417⟩,⟨(-926210242138311341990077449174),(-926210242138311341956626214496)⟩⟩
lemma root831_contains : root831.Contains (rootPhase 831) := by
  have hh := CBox.mul_contains mid831_contains root1_contains (c:=root831) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def root832 : CBox := ⟨⟨382683432365089771715348698550,382683432365089771748644840782⟩,⟨(-923879532511286756143228206166),(-923879532511286756110208132241)⟩⟩
lemma root832_contains : root832.Contains (rootPhase 832) := by
  have hh := CBox.mul_contains root416_contains root416_contains (c:=root832) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def mid833 : CBox := root832
lemma mid833_contains : mid833.Contains (rootPhase 832) := root832_contains
def root833 : CBox := ⟨⟨388345046698826291611767396997,388345046698826291645283624187⟩,⟨(-921514039342041943480523526835),(-921514039342041943447292174631)⟩⟩
lemma root833_contains : root833.Contains (rootPhase 833) := by
  have hh := CBox.mul_contains mid833_contains root1_contains (c:=root833) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def root834 : CBox := ⟨⟨393992040061048108582967018365,393992040061048108616464302021⟩,⟨(-919113851690057743923574603207),(-919113851690057743890357100651)⟩⟩
lemma root834_contains : root834.Contains (rootPhase 834) := by
  have hh := CBox.mul_contains root417_contains root417_contains (c:=root834) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def mid835 : CBox := root834
lemma mid835_contains : mid835.Contains (rootPhase 834) := root834_contains
def root835 : CBox := ⟨⟨399624199845646828530779662107,399624199845646828564498146672⟩,⟨(-916679059921042663131636740237),(-916679059921042663098206508562)⟩⟩
lemma root835_contains : root835.Contains (rootPhase 835) := by
  have hh := CBox.mul_contains mid835_contains root1_contains (c:=root835) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def root836 : CBox := ⟨⟨405241314004989870895300987607,405241314004989870928694809067⟩,⟨(-914209755703530654650010710669),(-914209755703530654616901279000)⟩⟩
lemma root836_contains : root836.Contains (rootPhase 836) := by
  have hh := CBox.mul_contains root418_contains root418_contains (c:=root836) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def mid837 : CBox := root836
lemma mid837_contains : mid837.Contains (rootPhase 836) := root836_contains
def root837 : CBox := ⟨⟨410843171057903942170170698247,410843171057903942203784965080⟩,⟨(-911706032005429851419475925637),(-911706032005429851386154178449)⟩⟩
lemma root837_contains : root837.Contains (rootPhase 837) := by
  have hh := CBox.mul_contains mid837_contains root1_contains (c:=root837) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def root838 : CBox := ⟨⟨416429560097637182549308351946,416429560097637182582900600125⟩,⟨(-909167983090522376578931508971),(-909167983090522376545626659620)⟩⟩
lemma root838_contains : root838.Contains (rootPhase 838) := by
  have hh := CBox.mul_contains root419_contains root419_contains (c:=root838) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def mid839 : CBox := root838
lemma mid839_contains : mid839.Contains (rootPhase 838) := root838_contains
def root839 : CBox := ⟨⟨422000270799799685927880863691,422000270799799685961694655494⟩,⟨(-906595704514915365348090762100),(-906595704514915365314572165397)⟩⟩
lemma root839_contains : root839.Contains (rootPhase 839) := by
  have hh := CBox.mul_contains mid839_contains root1_contains (c:=root839) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def root840 : CBox := ⟨⟨427555093430282094307754535541,427555093430282094341167009588⟩,⟨(-903989293123443331601102248756),(-903989293123443331567993274107)⟩⟩
lemma root840_contains : root840.Contains (rootPhase 840) := by
  have hh := CBox.mul_contains root420_contains root420_contains (c:=root840) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def mid841 : CBox := root840
lemma mid841_contains : mid841.Contains (rootPhase 840) := root840_contains
def root841 : CBox := ⟨⟨433093818853151968470894136181,433093818853151968504526855616⟩,⟨(-901348847046022014585731077271),(-901348847046022014552409237913)⟩⟩
lemma root841_contains : root841.Contains (rootPhase 841) := by
  have hh := CBox.mul_contains mid841_contains root1_contains (c:=root841) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def root842 : CBox := ⟨⟨438616238538527637633703448009,438616238538527637667311313825⟩,⟨(-898674465693953843056928334003),(-898674465693953843023626506497)⟩⟩
lemma root842_contains : root842.Contains (rootPhase 842) := by
  have hh := CBox.mul_contains root421_contains root421_contains (c:=root842) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def mid843 : CBox := root842
lemma mid843_contains : mid843.Contains (rootPhase 842) := root842_contains
def root843 : CBox := ⟨⟨444122144570429231628630097256,444122144570429231662459285679⟩,⟨(-895966249756185155929595635457),(-895966249756185155896079532502)⟩⟩
lemma root843_contains : root843.Contains (rootPhase 843) := by
  have hh := CBox.mul_contains mid843_contains root1_contains (c:=root843) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def root844 : CBox := ⟨⟨449611329654606600033016431283,449611329654606600066510222922⟩,⟨(-893224301195515320357262433806),(-893224301195515320324078344724)⟩⟩
lemma root844_contains : root844.Contains (rootPhase 844) := by
  have hh := CBox.mul_contains root422_contains root422_contains (c:=root844) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def mid845 : CBox := root844
lemma mid845_contains : mid845.Contains (rootPhase 844) := root844_contains
def root845 : CBox := ⟨⟨455083587126343823522474189342,455083587126343823556188478227⟩,⟨(-890448723244757889967080097235),(-890448723244757889933682216275)⟩⟩
lemma root845_contains : root845.Contains (rootPhase 845) := by
  have hh := CBox.mul_contains mid845_contains root1_contains (c:=root845) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def root846 : CBox := ⟨⟨460538710958240023619793564025,460538710958240023653479865568⟩,⟨(-887639620402853947775076290913),(-887639620402853947741701480009)⟩⟩
lemma root846_contains : root846.Contains (rootPhase 846) := by
  have hh := CBox.mul_contains root423_contains root423_contains (c:=root846) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def mid847 : CBox := root846
lemma mid847_contains : mid847.Contains (rootPhase 846) := root846_contains
def root847 : CBox := ⟨⟨465976495767966177889250370171,465976495767966177923158227867⟩,⟨(-884797098430937780118985994219),(-884797098430937780085396000989)⟩⟩
lemma root847_contains : root847.Contains (rootPhase 847) := by
  have hh := CBox.mul_contains mid847_contains root1_contains (c:=root847) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def root848 : CBox := ⟨⟨471396736825997648543093784172,471396736825997648576563635797⟩,⟨(-881921264348355029727487766549),(-881921264348355029694347289201)⟩⟩
lemma root848_contains : root848.Contains (rootPhase 848) := by
  have hh := CBox.mul_contains root424_contains root424_contains (c:=root848) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def mid849 : CBox := root848
lemma mid849_contains : mid849.Contains (rootPhase 848) := root848_contains
def root849 : CBox := ⟨⟨476799230063322133328746963425,476799230063322133362436827096⟩,⟨(-879012226428633477846138375457),(-879012226428633477812783828037)⟩⟩
lemma root849_contains : root849.Contains (rootPhase 849) := by
  have hh := CBox.mul_contains mid849_contains root1_contains (c:=root849) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def root850 : CBox := ⟨⟨482183772079122748503941267700,482183772079122748537600324716⟩,⟨(-876070094195406607110622603269),(-876070094195406607077294209259)⟩⟩
lemma root850_contains : root850.Contains (rootPhase 850) := by
  have hh := CBox.mul_contains root425_contains root425_contains (c:=root850) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def mid851 : CBox := root850
lemma mid851_contains : mid851.Contains (rootPhase 850) := root850_contains
def root851 : CBox := ⟨⟨487550160148435954627963671261,487550160148435954661843776854⟩,⟨(-873094978418290098650948795514),(-873094978418290098617404963987)⟩⟩
lemma root851_contains : root851.Contains (rootPhase 851) := by
  have hh := CBox.mul_contains mid851_contains root1_contains (c:=root851) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def root852 : CBox := ⟨⟨492898192229784036859670372840,492898192229784036893204848373⟩,⟨(-870086991108711418666960677167),(-870086991108711418633759527631)⟩⟩
lemma root852_contains : root852.Contains (rootPhase 852) := by
  have hh := CBox.mul_contains root426_contains root426_contains (c:=root852) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def mid853 : CBox := root852
lemma mid853_contains : mid853.Contains (rootPhase 852) := root852_contains
def root853 : CBox := ⟨⟨498227666972781852397509544969,498227666972781852431264175137⟩,⟨(-867046245515692651494948159099),(-867046245515692651461532125462)⟩⟩
lemma root853_contains : root853.Contains (rootPhase 853) := by
  have hh := CBox.mul_contains mid853_contains root1_contains (c:=root853) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def root854 : CBox := ⟨⟨503538383725717558678401655568,503538383725717558712122293526⟩,⟨(-863972856121586737932861816060),(-863972856121586737899474997272)⟩⟩
lemma root854_contains : root854.Contains (rootPhase 854) := by
  have hh := CBox.mul_contains root427_contains root427_contains (c:=root854) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def mid855 : CBox := root854
lemma mid855_contains : mid855.Contains (rootPhase 854) := root854_contains
def root855 : CBox := ⟨⟨508830142543107036918165078865,508830142543107036952106889098⟩,⟨(-860866938637767279359383618760),(-860866938637767279325780569957)⟩⟩
lemma root855_contains : root855.Contains (rootPhase 855) := by
  have hh := CBox.mul_contains mid855_contains root1_contains (c:=root855) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def root856 : CBox := ⟨⟨514102744193221726580312444780,514102744193221726613831752624⟩,⟨(-857728610000272069916828783410),(-857728610000272069883661404293)⟩⟩
lemma root856_contains : root856.Contains (rootPhase 856) := by
  have hh := CBox.mul_contains root428_contains root428_contains (c:=root856) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def mid857 : CBox := root856
lemma mid857_contains : mid857.Contains (rootPhase 856) := root856_contains
def root857 : CBox := ⟨⟨519355990165589587348330127313,519355990165589587382069144113⟩,⟨(-854557988365400520782505596872),(-854557988365400520749123013309)⟩⟩
lemma root857_contains : root857.Contains (rootPhase 857) := by
  have hh := CBox.mul_contains mid857_contains root1_contains (c:=root857) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def root858 : CBox := ⟨⟨524589682678468906201608392055,524589682678468906235310518441⟩,⟨(-851355193105265142275894420363),(-851355193105265142242544159161)⟩⟩
lemma root858_contains : root858.Contains (rootPhase 858) := by
  have hh := CBox.mul_contains root429_contains root429_contains (c:=root858) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def mid859 : CBox := root858
lemma mid859_contains : mid859.Contains (rootPhase 858) := root858_contains
def root859 : CBox := ⟨⟨529803624686294668202445378655,529803624686294668236368209512⟩,⟨(-848120344803297251293822913582),(-848120344803297251260256125513)⟩⟩
lemma root859_contains : root859.Contains (rootPhase 859) := by
  have hh := CBox.mul_contains mid859_contains root1_contains (c:=root859) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def root860 : CBox := ⟨⟨534997619887097210649636566871,534997619887097210683203438925⟩,⟨(-844853565249707073274060901264),(-844853565249707073240847441172)⟩⟩
lemma root860_contains : root860.Contains (rootPhase 860) := by
  have hh := CBox.mul_contains root430_contains root430_contains (c:=root860) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def mid861 : CBox := root860
lemma mid861_contains : mid861.Contains (rootPhase 860) := root860_contains
def root861 : CBox := ⟨⟨540171472729892881284286090349,540171472729892881318072704321⟩,⟨(-841554977436898409618074208558),(-841554977436898409584644846381)⟩⟩
lemma root861_contains : root861.Contains (rootPhase 861) := by
  have hh := CBox.mul_contains mid861_contains root1_contains (c:=root861) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def root862 : CBox := ⟨⟨545324988422046422300438683632,545324988422046422334185172545⟩,⟨(-838224705554838043201530926909),(-838224705554838043168136949084)⟩⟩
lemma root862_contains : root862.Contains (rootPhase 862) := by
  have hh := CBox.mul_contains root431_contains root431_contains (c:=root862) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def mid863 : CBox := root862
lemma mid863_contains : mid863.Contains (rootPhase 862) := root862_contains
def root863 : CBox := ⟨⟨550457972936604802963621377356,550457972936604802997588584242⟩,⟨(-834862874986380056319021163678),(-834862874986380056285409984100)⟩⟩
lemma root863_contains : root863.Contains (rootPhase 863) := by
  have hh := CBox.mul_contains mid863_contains root1_contains (c:=root863) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def root864 : CBox := ⟨⟨555570233019602224729386160592,555570233019602224762886346768⟩,⟨(-831469612302545237093143395613),(-831469612302545237060016029004)⟩⟩
lemma root864_contains : root864.Contains (rootPhase 864) := by
  have hh := CBox.mul_contains root432_contains root432_contains (c:=root864) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def mid865 : CBox := root864
lemma mid865_contains : mid865.Contains (rootPhase 864) := root864_contains
def root865 : CBox := ⟨⟨560661576197336023826146287414,560661576197336023859865429627⟩,⟨(-828045045257755752081967737359),(-828045045257755752048624475927)⟩⟩
lemma root865_contains : root865.Contains (rootPhase 865) := by
  have hh := CBox.mul_contains mid865_contains root1_contains (c:=root865) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def root866 : CBox := ⟨⟨565731810783613197376212600871,565731810783613197409888772431⟩,⟨(-824589302785025264489201886169),(-824589302785025264455897052014)⟩⟩
lemma root866_contains : root866.Contains (rootPhase 866) := by
  have hh := CBox.mul_contains root433_contains root433_contains (c:=root866) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def mid867 : CBox := root866
lemma mid867_contains : mid867.Contains (rootPhase 866) := root866_contains
def root867 : CBox := ⟨⟨570780745886967280218980383391,570780745886967280252876463460⟩,⟨(-821102514991104679074914809510),(-821102514991104679041392806362)⟩⟩
lemma root867_contains : root867.Contains (rootPhase 867) := by
  have hh := CBox.mul_contains mid867_contains root1_contains (c:=root867) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def root868 : CBox := ⟨⟨575808191417845300732472515262,575808191417845300766002968862⟩,⟨(-817584813151583696519200535709),(-817584813151583696486041797693)⟩⟩
lemma root868_contains : root868.Contains (rootPhase 868) := by
  have hh := CBox.mul_contains root434_contains root434_contains (c:=root868) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def mid869 : CBox := root868
lemma mid869_contains : mid869.Contains (rootPhase 868) := root868_contains
def root869 : CBox := ⟨⟨580813958095764545061975466756,580813958095764545095724799606⟩,⟨(-814036329705948361668881913468),(-814036329705948361635506701813)⟩⟩
lemma root869_contains : root869.Contains (rootPhase 869) := by
  have hh := CBox.mul_contains mid869_contains root1_contains (c:=root869) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def root870 : CBox := ⟨⟨585797857456438860314473574395,585797857456438860348176660682⟩,⟨(-810457198252594791741025293763),(-810457198252594791707691564342)⟩⟩
lemma root870_contains : root870.Contains (rootPhase 870) := by
  have hh := CBox.mul_contains root435_contains root435_contains (c:=root870) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def mid871 : CBox := root870
lemma mid871_contains : mid871.Contains (rootPhase 870) := root870_contains
def root871 : CBox := ⟨⟨590759701858874228410160001363,590759701858874228444082899386⟩,⟨(-806847553543799272220922453354),(-806847553543799272187371000041)⟩⟩
lemma root871_contains : root871.Contains (rootPhase 871) := by
  have hh := CBox.mul_contains mid871_contains root1_contains (c:=root871) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def root872 : CBox := ⟨⟨595699304492433343453518761923,595699304492433343486999595164⟩,⟨(-803207531480644909820831966987),(-803207531480644909787740813247)⟩⟩
lemma root872_contains : root872.Contains (rootPhase 872) := by
  have hh := CBox.mul_contains root436_contains root436_contains (c:=root872) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def mid873 : CBox := root872
lemma mid873_contains : mid873.Contains (rootPhase 872) := root872_contains
def root873 : CBox := ⟨⟨600616479383868926640237987708,600616479383868926673937008066⟩,⟨(-799537269107905033514487472517),(-799537269107905033481179761484)⟩⟩
lemma root873_contains : root873.Contains (rootPhase 873) := by
  have hh := CBox.mul_contains mid873_contains root1_contains (c:=root873) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def root874 : CBox := ⟨⟨605511041404325513907002424347,605511041404325513940652258593⟩,⟨(-795836904608883536276988428168),(-795836904608883536243725278860)⟩⟩
lemma root874_contains : root874.Contains (rootPhase 874) := by
  have hh := CBox.mul_contains root437_contains root437_contains (c:=root874) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def mid875 : CBox := root874
lemma mid875_contains : mid875.Contains (rootPhase 874) := root874_contains
def root875 : CBox := ⟨⟨610382806276309452702606729614,610382806276309452736475660378⟩,⟨(-792106577300212351796625882238),(-792106577300212351763144951119)⟩⟩
lemma root875_contains : root875.Contains (rootPhase 875) := by
  have hh := CBox.mul_contains mid875_contains root1_contains (c:=root875) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def root876 : CBox := ⟨⟨615231590580626845471344363707,615231590580626845504837826800⟩,⟨(-788346427626606262023238736236),(-788346427626606261990131046242)⟩⟩
lemma root876_contains : root876.Contains (rootPhase 876) := by
  have hh := CBox.mul_contains root438_contains root438_contains (c:=root876) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def mid877 : CBox := root876
lemma mid877_contains : mid877.Contains (rootPhase 876) := root876_contains
def root877 : CBox := ⟨⟨620057211763289178632578325584,620057211763289178666289789142⟩,⟨(-784556597155575233038052809312),(-784556597155575233004728105069)⟩⟩
lemma root877_contains : root877.Contains (rootPhase 877) := by
  have hh := CBox.mul_contains mid877_contains root1_contains (c:=root877) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def root878 : CBox := ⟨⟨624859488142386377070397381018,624859488142386377104056343660⟩,⟨(-780737228572094478315702661215),(-780737228572094478282425564596)⟩⟩
lemma root878_contains : root878.Contains (rootPhase 878) := by
  have hh := CBox.mul_contains root439_contains root439_contains (c:=root878) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def mid879 : CBox := root878
lemma mid879_contains : mid879.Contains (rootPhase 878) := root878_contains
def root879 : CBox := ⟨⟨629638238914927025359184486748,629638238914927025393062338749⟩,⟨(-776888465673232450055029064835),(-776888465673232450021533754509)⟩⟩
lemma root879_contains : root879.Contains (rootPhase 879) := by
  have hh := CBox.mul_contains mid879_contains root1_contains (c:=root879) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def root880 : CBox := ⟨⟨634393284163645498201601968286,634393284163645498235001146488⟩,⟨(-773010453362736960824835229796),(-773010453362736960791840542110)⟩⟩
lemma root880_contains : root880.Contains (rootPhase 880) := by
  have hh := CBox.mul_contains root440_contains root440_contains (c:=root880) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def mid881 : CBox := root880
lemma mid881_contains : mid881.Contains (rootPhase 880) := root880_contains
def root881 : CBox := ⟨⟨639124444863775743787797760485,639124444863775743821413950350⟩,⟨(-769103337645579639360640996662),(-769103337645579639327429498654)⟩⟩
lemma root881_contains : root881.Contains (rootPhase 881) := by
  have hh := CBox.mul_contains mid881_contains root1_contains (c:=root881) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def root882 : CBox := ⟨⟨643831542889791465054410887208,643831542889791465087971694391⟩,⟨(-765167265622458925902783576421),(-765167265622458925869622692752)⟩⟩
lemma root882_contains : root882.Contains (rootPhase 882) := by
  have hh := CBox.mul_contains root441_contains root441_contains (c:=root882) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def mid883 : CBox := root882
lemma mid883_contains : mid883.Contains (rootPhase 882) := root882_contains
def root883 : CBox := ⟨⟨648514401022112445070763848432,648514401022112445104542531949⟩,⟨(-761202385484261814043764415935),(-761202385484261814010385549911)⟩⟩
lemma root883_contains : root883.Contains (rootPhase 883) := by
  have hh := CBox.mul_contains mid883_contains root1_contains (c:=root883) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def root884 : CBox := ⟨⟨653172842953776764070585908986,653172842953776764103979914394⟩,⟨(-757208846506484547589305439391),(-757208846506484547556309098857)⟩⟩
lemma root884_contains : root884.Contains (rootPhase 884) := by
  have hh := CBox.mul_contains root442_contains root442_contains (c:=root884) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def mid885 : CBox := root884
lemma mid885_contains : mid885.Contains (rootPhase 884) := root884_contains
def root885 : CBox := ⟨⟨657806693297078656917443907127,657806693297078656951054628080⟩,⟨(-753186799043612482497358568526),(-753186799043612482464145084501)⟩⟩
lemma root885_contains : root885.Contains (rootPhase 885) := by
  have hh := CBox.mul_contains mid885_contains root1_contains (c:=root885) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def root886 : CBox := ⟨⟨662415777590171761099347777987,662415777590171761132899770125⟩,⟨(-749136394523459325483082701336),(-749136394523459325449922861402)⟩⟩
lemma root886_contains : root886.Contains (rootPhase 886) := by
  have hh := CBox.mul_contains root443_contains root443_contains (c:=root886) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def mid887 : CBox := root886
lemma mid887_contains : mid887.Contains (rootPhase 886) := root886_contains
def root887 : CBox := ⟨⟨666999922303637506636310204049,666999922303637506670079755420⟩,⟨(-745057785441465962421874142598),(-745057785441465962388496013285)⟩⟩
lemma root887_contains : root887.Contains (rootPhase 887) := by
  have hh := CBox.mul_contains mid887_contains root1_contains (c:=root887) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def root888 : CBox := ⟨⟨671558954847018400611749515103,671558954847018400645058999029⟩,⟨(-740951125354959091189320253934),(-740951125354959091156425683405)⟩⟩
lemma root888_contains : root888.Contains (rootPhase 888) := by
  have hh := CBox.mul_contains root444_contains root444_contains (c:=root888) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def mid889 : CBox := root888
lemma mid889_contains : mid889.Contains (rootPhase 888) := root888_contains
def root889 : CBox := ⟨⟨676092703575315960346670500447,676092703575315960380195761740⟩,⟨(-736816568877369875103922733569),(-736816568877369875070811179056)⟩⟩
lemma root889_contains : root889.Contains (rootPhase 889) := by
  have hh := CBox.mul_contains mid889_contains root1_contains (c:=root889) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def root890 : CBox := ⟨⟨680600997795453050580698926293,680600997795453050614162499791⟩,⟨(-732654271672412834629286952252),(-732654271672412834596232072792)⟩⟩
lemma root890_contains : root890.Contains (rootPhase 890) := by
  have hh := CBox.mul_contains root445_contains root445_contains (c:=root890) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def mid891 : CBox := root890
lemma mid891_contains : mid891.Contains (rootPhase 890) := root890_contains
def root891 : CBox := ⟨⟨685083667772700381348198901907,685083667772700381381879072544⟩,⟨(-728464390448225196505863282943),(-728464390448225196472590301418)⟩⟩
lemma root891_contains : root891.Contains (rootPhase 891) := by
  have hh := CBox.mul_contains mid891_contains root1_contains (c:=root891) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def root892 : CBox := ⟨⟨689540544737066924603060005837,689540544737066924636346224050⟩,⟨(-724247082951466920954679776727),(-724247082951466920921798530517)⟩⟩
lemma root892_contains : root892.Contains (rootPhase 892) := by
  have hh := CBox.mul_contains root446_contains root446_contains (c:=root892) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def mid893 : CBox := root892
lemma mid893_contains : mid893.Contains (rootPhase 892) := root892_contains
def root893 : CBox := ⟨⟨693971460889654008989941970715,693971460889654009023443560880⟩,⟨(-720002507961381629090380748891),(-720002507961381629057282311974)⟩⟩
lemma root893_contains : root893.Contains (rootPhase 893) := by
  have hh := CBox.mul_contains mid893_contains root1_contains (c:=root893) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def root894 : CBox := ⟨⟨698376249408972853541039356989,698376249408972853574475885141⟩,⟨(-715730825283818654139179218556),(-715730825283818654106140467687)⟩⟩
lemma root894_contains : root894.Contains (rootPhase 894) := by
  have hh := CBox.mul_contains root447_contains root447_contains (c:=root894) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def mid895 : CBox := root894
lemma mid895_contains : mid895.Contains (rootPhase 894) := root894_contains
def root895 : CBox := ⟨⟨702754744457225302439017780633,702754744457225302472670479060⟩,⟨(-711432195745216441535864781433),(-711432195745216441502607748976)⟩⟩
lemma root895_contains : root895.Contains (rootPhase 895) := by
  have hh := CBox.mul_contains mid895_contains root1_contains (c:=root895) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def root896 : CBox := ⟨⟨707106781186547524387186693326,707106781186547524420332330671⟩,⟨(-707106781186547524414290323937),(-707106781186547524381568000087)⟩⟩
lemma root896_contains : root896.Contains (rootPhase 896) := by
  have hh := CBox.mul_contains root448_contains root448_contains (c:=root896) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def mid897 : CBox := root896
lemma mid897_contains : mid897.Contains (rootPhase 896) := root896_contains
def root897 : CBox := ⟨⟨711432195745216441508350878881,711432195745216441541710583020⟩,⟨(-702754744457225302466447613192),(-702754744457225302433508617176)⟩⟩
lemma root897_contains : root897.Contains (rootPhase 897) := by
  have hh := CBox.mul_contains mid897_contains root1_contains (c:=root897) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def root898 : CBox := ⟨⟨715730825283818654111772310076,715730825283818654145064103009⟩,⟨(-698376249408972853568294362734),(-698376249408972853535417962467)⟩⟩
lemma root898_contains : root898.Contains (rootPhase 898) := by
  have hh := CBox.mul_contains root449_contains root449_contains (c:=root898) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def mid899 : CBox := root898
lemma mid899_contains : mid899.Contains (rootPhase 898) := root898_contains
def root899 : CBox := ⟨⟨720002507961381629062800258289,720002507961381629096306891167⟩,⟨(-693971460889654009017303152579),(-693971460889654008984209018855)⟩⟩
lemma root899_contains : root899.Contains (rootPhase 899) := by
  have hh := CBox.mul_contains mid899_contains root1_contains (c:=root899) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def root900 : CBox := ⟨⟨724247082951466920927372541369,724247082951466920960476785348⟩,⟨(-689540544737066924630078480354),(-689540544737066924597384393170)⟩⟩
lemma root900_contains : root900.Contains (rootPhase 900) := by
  have hh := CBox.mul_contains root450_contains root450_contains (c:=root900) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def mid901 : CBox := root900
lemma mid901_contains : mid901.Contains (rootPhase 900) := root900_contains
def root901 : CBox := ⟨⟨728464390448225196478216654684,728464390448225196511534451924⟩,⟨(-685083667772700381375487955058),(-685083667772700381342577116487)⟩⟩
lemma root901_contains : root901.Contains (rootPhase 901) := by
  have hh := CBox.mul_contains mid901_contains root1_contains (c:=root901) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def root902 : CBox := ⟨⟨732654271672412834601748066115,732654271672412834634994558601⟩,⟨(-680600997795453050607812343777),(-680600997795453050574967085142)⟩⟩
lemma root902_contains : root902.Contains (rootPhase 902) := by
  have hh := CBox.mul_contains root451_contains root451_contains (c:=root902) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def mid903 : CBox := root902
lemma mid903_contains : mid903.Contains (rootPhase 902) := root902_contains
def root903 : CBox := ⟨⟨736816568877369875076211185061,736816568877369875109671982096⟩,⟨(-676092703575315960373889334387),(-676092703575315960340826291257)⟩⟩
lemma root903_contains : root903.Contains (rootPhase 903) := by
  have hh := CBox.mul_contains mid903_contains root1_contains (c:=root903) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def root904 : CBox := ⟨⟨740951125354959091161917806146,740951125354959091194902620832⟩,⟨(-671558954847018400638573921097),(-671558954847018400606015774573)⟩⟩
lemma root904_contains : root904.Contains (rootPhase 904) := by
  have hh := CBox.mul_contains root452_contains root452_contains (c:=root904) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def mid905 : CBox := root904
lemma mid905_contains : mid905.Contains (rootPhase 904) := root904_contains
def root905 : CBox := ⟨⟨745057785441465962394086138412,745057785441465962427283325263⟩,⟨(-666999922303637506663438955444),(-666999922303637506630664463682)⟩⟩
lemma root905_contains : root905.Contains (rootPhase 905) := by
  have hh := CBox.mul_contains mid905_contains root1_contains (c:=root905) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def root906 : CBox := ⟨⟨749136394523459325455403173529,749136394523459325488526101030⟩,⟨(-662415777590171761126299849933),(-662415777590171761093593898538)⟩⟩
lemma root906_contains : root906.Contains (rootPhase 906) := by
  have hh := CBox.mul_contains root453_contains root453_contains (c:=root906) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def mid907 : CBox := root906
lemma mid907_contains : mid907.Contains (rootPhase 906) := root906_contains
def root907 : CBox := ⟨⟨753186799043612482469507665620,753186799043612482502843691986⟩,⟨(-657806693297078656944500620724),(-657806693297078656911577320660)⟩⟩
lemma root907_contains : root907.Contains (rootPhase 907) := by
  have hh := CBox.mul_contains mid907_contains root1_contains (c:=root907) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def root908 : CBox := ⟨⟨757208846506484547561730408134,757208846506484547594655419033⟩,⟨(-653172842953776764097296904049),(-653172842953776764064781998954)⟩⟩
lemma root908_contains : root908.Contains (rootPhase 908) := by
  have hh := CBox.mul_contains root454_contains root454_contains (c:=root908) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def mid909 : CBox := root908
lemma mid909_contains : mid909.Contains (rootPhase 908) := root908_contains
def root909 : CBox := ⟨⟨761202385484261814015853835948,761202385484261814048990597622⟩,⟨(-648514401022112445097742401548),(-648514401022112445065011202030)⟩⟩
lemma root909_contains : root909.Contains (rootPhase 909) := by
  have hh := CBox.mul_contains mid909_contains root1_contains (c:=root909) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def root910 : CBox := ⟨⟨765167265622458925874982210526,765167265622458925908041302540⟩,⟨(-643831542889791465081212062197),(-643831542889791465048552358778)⟩⟩
lemma root910_contains : root910.Contains (rootPhase 910) := by
  have hh := CBox.mul_contains root455_contains root455_contains (c:=root910) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def mid911 : CBox := root910
lemma mid911_contains : mid911.Contains (rootPhase 910) := root910_contains
def root911 : CBox := ⟨⟨769103337645579639332669284213,769103337645579639365940831429⟩,⟨(-639124444863775743814702806797),(-639124444863775743781825834663)⟩⟩
lemma root911_contains : root911.Contains (rootPhase 911) := by
  have hh := CBox.mul_contains mid911_contains root1_contains (c:=root911) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def root912 : CBox := ⟨⟨773010453362736960797188758524,773010453362736960829948613335⟩,⟨(-634393284163645498228093943459),(-634393284163645498195761670695)⟩⟩
lemma root912_contains : root912.Contains (rootPhase 912) := by
  have hh := CBox.mul_contains root456_contains root456_contains (c:=root912) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def mid913 : CBox := root912
lemma mid913_contains : mid913.Contains (rootPhase 912) := root912_contains
def root913 : CBox := ⟨⟨776888465673232450026987940943,776888465673232450059958064088⟩,⟨(-629638238914927025385991618591),(-629638238914927025353443754987)⟩⟩
lemma root913_contains : root913.Contains (rootPhase 913) := by
  have hh := CBox.mul_contains mid913_contains root1_contains (c:=root913) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def root914 : CBox := ⟨⟨780737228572094478287771502152,780737228572094478320661104170⟩,⟨(-624859488142386377097026164383),(-624859488142386377064552639421)⟩⟩
lemma root914_contains : root914.Contains (rootPhase 914) := by
  have hh := CBox.mul_contains root457_contains root457_contains (c:=root914) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def mid915 : CBox := root914
lemma mid915_contains : mid915.Contains (rootPhase 914) := root914_contains
def root915 : CBox := ⟨⟨784556597155575233009952776226,784556597155575233043053325536⟩,⟨(-620057211763289178659310134322),(-620057211763289178626620075307)⟩⟩
lemma root915_contains : root915.Contains (rootPhase 915) := by
  have hh := CBox.mul_contains mid915_contains root1_contains (c:=root915) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def root916 : CBox := ⟨⟨788346427626606261995416863831,788346427626606262028098527925⟩,⟨(-615231590580626845497727967455),(-615231590580626845465453820840)⟩⟩
lemma root916_contains : root916.Contains (rootPhase 916) := by
  have hh := CBox.mul_contains root458_contains root458_contains (c:=root916) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def mid917 : CBox := root916
lemma mid917_contains : mid917.Contains (rootPhase 916) := root916_contains
def root917 : CBox := ⟨⟨792106577300212351768472638888,792106577300212351801363843666⟩,⟨(-610382806276309452729254768056),(-610382806276309452696765212069)⟩⟩
lemma root917_contains : root917.Contains (rootPhase 917) := by
  have hh := CBox.mul_contains mid917_contains root1_contains (c:=root917) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def root918 : CBox := ⟨⟨795836904608883536248945876225,795836904608883536281753140950⟩,⟨(-605511041404325513933471527240),(-605511041404325513901059229973)⟩⟩
lemma root918_contains : root918.Contains (rootPhase 918) := by
  have hh := CBox.mul_contains root459_contains root459_contains (c:=root918) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def mid919 : CBox := root918
lemma mid919_contains : mid919.Contains (rootPhase 918) := root918_contains
def root919 : CBox := ⟨⟨799537269107905033486277183712,799537269107905033519294645445⟩,⟨(-600616479383868926666809334060),(-600616479383868926634180714234)⟩⟩
lemma root919_contains : root919.Contains (rootPhase 919) := by
  have hh := CBox.mul_contains mid919_contains root1_contains (c:=root919) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def root920 : CBox := ⟨⟨803207531480644909792934418217,803207531480644909825461869280⟩,⟨(-595699304492433343479688496710),(-595699304492433343447584387550)⟩⟩
lemma root920_contains : root920.Contains (rootPhase 920) := by
  have hh := CBox.mul_contains root460_contains root460_contains (c:=root920) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def mid921 : CBox := root920
lemma mid921_contains : mid921.Contains (rootPhase 920) := root920_contains
def root921 : CBox := ⟨⟨806847553543799272192649965686,806847553543799272225385537234⟩,⟨(-590759701858874228436628132325),(-590759701858874228404309268946)⟩⟩
lemma root921_contains : root921.Contains (rootPhase 921) := by
  have hh := CBox.mul_contains mid921_contains root1_contains (c:=root921) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def root922 : CBox := ⟨⟨810457198252594791712864189338,810457198252594791745512893763⟩,⟨(-585797857456438860340761972453),(-585797857456438860308523237436)⟩⟩
lemma root922_contains : root922.Contains (rootPhase 922) := by
  have hh := CBox.mul_contains root461_contains root461_contains (c:=root922) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def mid923 : CBox := root922
lemma mid923_contains : mid923.Contains (rootPhase 922) := root922_contains
def root923 : CBox := ⟨⟨814036329705948361640554597961,814036329705948361673412054083⟩,⟨(-580813958095764545088365294868),(-580813958095764545055910923782)⟩⟩
lemma root923_contains : root923.Contains (rootPhase 923) := by
  have hh := CBox.mul_contains mid923_contains root1_contains (c:=root923) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def root924 : CBox := ⟨⟨817584813151583696491153576539,817584813151583696523584244786⟩,⟨(-575808191417845300758511989072),(-575808191417845300726480930220)⟩⟩
lemma root924_contains : root924.Contains (rootPhase 924) := by
  have hh := CBox.mul_contains root462_contains root462_contains (c:=root924) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def mid925 : CBox := root924
lemma mid925_contains : mid925.Contains (rootPhase 924) := root924_contains
def root925 : CBox := ⟨⟨821102514991104679046541120987,821102514991104679079179076465⟩,⟨(-570780745886967280245280885745),(-570780745886967280213035386770)⟩⟩
lemma root925_contains : root925.Contains (rootPhase 925) := by
  have hh := CBox.mul_contains mid925_contains root1_contains (c:=root925) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def root926 : CBox := ⟨⟨824589302785025264460940297301,824589302785025264493487961739⟩,⟨(-565731810783613197402332893947),(-565731810783613197370170405313)⟩⟩
lemma root926_contains : root926.Contains (rootPhase 926) := by
  have hh := CBox.mul_contains root463_contains root463_contains (c:=root926) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def mid927 : CBox := root926
lemma mid927_contains : mid927.Contains (rootPhase 926) := root926_contains
def root927 : CBox := ⟨⟨828045045257755752053541181138,828045045257755752086296741039⟩,⟨(-560661576197336023852367217492),(-560661576197336023819989437761)⟩⟩
lemma root927_contains : root927.Contains (rootPhase 927) := by
  have hh := CBox.mul_contains mid927_contains root1_contains (c:=root927) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def root928 : CBox := ⟨⟨831469612302545237065049549524,831469612302545237097271623935⟩,⟨(-555570233019602224755183174975),(-555570233019602224723377796968)⟩⟩
lemma root928_contains : root928.Contains (rootPhase 928) := by
  have hh := CBox.mul_contains root464_contains root464_contains (c:=root928) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def mid929 : CBox := root928
lemma mid929_contains : mid929.Contains (rootPhase 928) := root928_contains
def root929 : CBox := ⟨⟨834862874986380056290540502254,834862874986380056322968089383⟩,⟨(-550457972936604802989730639976),(-550457972936604802957711828797)⟩⟩
lemma root929_contains : root929.Contains (rootPhase 929) := by
  have hh := CBox.mul_contains mid929_contains root1_contains (c:=root929) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def root930 : CBox := ⟨⟨838224705554838043173163073836,838224705554838043205497599254⟩,⟨(-545324988422046422326367012101),(-545324988422046422294433912186)⟩⟩
lemma root930_contains : root930.Contains (rootPhase 930) := by
  have hh := CBox.mul_contains root465_contains root465_contains (c:=root930) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def mid931 : CBox := root930
lemma mid931_contains : mid931.Contains (rootPhase 930) := root930_contains
def root931 : CBox := ⟨⟨841554977436898409589543123165,841554977436898409622083743534⟩,⟨(-540171472729892881310314147745),(-540171472729892881278166796398)⟩⟩
lemma root931_contains : root931.Contains (rootPhase 931) := by
  have hh := CBox.mul_contains mid931_contains root1_contains (c:=root931) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def root932 : CBox := ⟨⟨844853565249707073245811981464,844853565249707073277918852018⟩,⟨(-534997619887097210675312706953),(-534997619887097210643595052171)⟩⟩
lemma root932_contains : root932.Contains (rootPhase 932) := by
  have hh := CBox.mul_contains root466_contains root466_contains (c:=root932) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def mid933 : CBox := root932
lemma mid933_contains : mid933.Contains (rootPhase 932) := root932_contains
def root933 : CBox := ⟨⟨848120344803297251265252215192,848120344803297251297563662078⟩,⟨(-529803624686294668228379055750),(-529803624686294668196448414145)⟩⟩
lemma root933_contains : root933.Contains (rootPhase 933) := by
  have hh := CBox.mul_contains mid933_contains root1_contains (c:=root933) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def root934 : CBox := ⟨⟨851355193105265142247437235290,851355193105265142279652200595⟩,⟨(-524589682678468906227360770765),(-524589682678468906195518676430)⟩⟩
lemma root934_contains : root934.Contains (rootPhase 934) := by
  have hh := CBox.mul_contains root467_contains root467_contains (c:=root934) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def mid935 : CBox := root934
lemma mid935_contains : mid935.Contains (rootPhase 934) := root934_contains
def root935 : CBox := ⟨⟨854557988365400520753886529215,854557988365400520786306629815⟩,⟨(-519355990165589587374181429725),(-519355990165589587342125561949)⟩⟩
lemma root935_contains : root935.Contains (rootPhase 935) := by
  have hh := CBox.mul_contains mid935_contains root1_contains (c:=root935) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def root936 : CBox := ⟨⟨857728610000272069888524808331,857728610000272069920443298268⟩,⟨(-514102744193221726605756834780),(-514102744193221726574242796988)⟩⟩
lemma root936_contains : root936.Contains (rootPhase 936) := by
  have hh := CBox.mul_contains root468_contains root468_contains (c:=root936) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def mid937 : CBox := root936
lemma mid937_contains : mid937.Contains (rootPhase 936) := root936_contains
def root937 : CBox := ⟨⟨860866938637767279330716872332,860866938637767279362838286120⟩,⟨(-508830142543107036943900885216),(-508830142543107036912174763760)⟩⟩
lemma root937_contains : root937.Contains (rootPhase 937) := by
  have hh := CBox.mul_contains mid937_contains root1_contains (c:=root937) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def root938 : CBox := ⟨⟨863972856121586737904309230369,863972856121586737936331287626⟩,⟨(-503538383725717558703955614020),(-503538383725717558672320797226)⟩⟩
lemma root938_contains : root938.Contains (rootPhase 938) := by
  have hh := CBox.mul_contains root469_contains root469_contains (c:=root938) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def mid939 : CBox := root938
lemma mid939_contains : mid939.Contains (rootPhase 938) := root938_contains
def root939 : CBox := ⟨⟨867046245515692651466235448460,867046245515692651498460963064⟩,⟨(-498227666972781852423161577064),(-498227666972781852391313922749)⟩⟩
lemma root939_contains : root939.Contains (rootPhase 939) := by
  have hh := CBox.mul_contains mid939_contains root1_contains (c:=root939) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def root940 : CBox := ⟨⟨870086991108711418638531891522,870086991108711418670316553204⟩,⟨(-492898192229784036884969223766),(-492898192229784036853557633021)⟩⟩
lemma root940_contains : root940.Contains (rootPhase 940) := by
  have hh := CBox.mul_contains root470_contains root470_contains (c:=root940) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def mid941 : CBox := root940
lemma mid941_contains : mid941.Contains (rootPhase 940) := root940_contains
def root941 : CBox := ⟨⟨873094978418290098622203629848,873094978418290098654190176519⟩,⟨(-487550160148435954653516286856),(-487550160148435954621893192919)⟩⟩
lemma root941_contains : root941.Contains (rootPhase 941) := by
  have hh := CBox.mul_contains mid941_contains root1_contains (c:=root941) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def root942 : CBox := ⟨⟨876070094195406607081992293130,876070094195406607113876070500⟩,⟨(-482183772079122748529311781549),(-482183772079122748497782780687)⟩⟩
lemma root942_contains : root942.Contains (rootPhase 942) := by
  have hh := CBox.mul_contains root471_contains root471_contains (c:=root942) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def mid943 : CBox := root942
lemma mid943_contains : mid943.Contains (rootPhase 942) := root942_contains
def root943 : CBox := ⟨⟨879012226428633477817349393579,879012226428633477849435565882⟩,⟨(-476799230063322133354214733980),(-476799230063322133322473508444)⟩⟩
lemma root943_contains : root943.Contains (rootPhase 943) := by
  have hh := CBox.mul_contains mid943_contains root1_contains (c:=root943) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def root944 : CBox := ⟨⟨881921264348355029699029074278,881921264348355029730579646271⟩,⟨(-471396736825997648568137517203),(-471396736825997648536976382508)⟩⟩
lemma root944_contains : root944.Contains (rootPhase 944) := by
  have hh := CBox.mul_contains root472_contains root472_contains (c:=root944) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def mid945 : CBox := root944
lemma mid945_contains : mid945.Contains (rootPhase 944) := root944_contains
def root945 : CBox := ⟨⟨884797098430937780090157885102,884797098430937780121908391075⟩,⟨(-465976495767966177914594543958),(-465976495767966177883223109231)⟩⟩
lemma root945_contains : root945.Contains (rootPhase 945) := by
  have hh := CBox.mul_contains mid945_contains root1_contains (c:=root945) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def root946 : CBox := ⟨⟨887639620402853947746363683317,887639620402853947778008695424⟩,⟨(-460538710958240023644955179335),(-460538710958240023613680430147)⟩⟩
lemma root946_contains : root946.Contains (rootPhase 946) := by
  have hh := CBox.mul_contains root473_contains root473_contains (c:=root946) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def mid947 : CBox := root946
lemma mid947_contains : mid947.Contains (rootPhase 946) := root946_contains
def root947 : CBox := ⟨⟨890448723244757889938210766129,890448723244757889970056196117⟩,⟨(-455083587126343823547732130096),(-455083587126343823516246393204)⟩⟩
lemma root947_contains : root947.Contains (rootPhase 947) := by
  have hh := CBox.mul_contains mid947_contains root1_contains (c:=root947) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def root948 : CBox := ⟨⟨893224301195515320328678418934,893224301195515320360076766705⟩,⟨(-449611329654606600057920502144),(-449611329654606600026876236486)⟩⟩
lemma root948_contains : root948.Contains (rootPhase 948) := by
  have hh := CBox.mul_contains root474_contains root474_contains (c:=root948) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def mid949 : CBox := root948
lemma mid949_contains : mid949.Contains (rootPhase 948) := root948_contains
def root949 : CBox := ⟨⟨895966249756185155900700955514,895966249756185155932298098771⟩,⟨(-444122144570429231653784051272),(-444122144570429231622530199359)⟩⟩
lemma root949_contains : root949.Contains (rootPhase 949) := by
  have hh := CBox.mul_contains mid949_contains root1_contains (c:=root949) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def root950 : CBox := ⟨⟨898674465693953843028149839048,898674465693953843059638091257⟩,⟨(-438616238538527637658674700865),(-438616238538527637627520268212)⟩⟩
lemma root950_contains : root950.Contains (rootPhase 950) := by
  have hh := CBox.mul_contains root475_contains root475_contains (c:=root950) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def mid951 : CBox := root950
lemma mid951_contains : mid951.Contains (rootPhase 950) := root950_contains
def root951 : CBox := ⟨⟨901348847046022014556797414167,901348847046022014588484921981⟩,⟨(-433093818853151968495960885050),(-433093818853151968464596211494)⟩⟩
lemma root951_contains : root951.Contains (rootPhase 951) := by
  have hh := CBox.mul_contains mid951_contains root1_contains (c:=root951) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def root952 : CBox := ⟨⟨903989293123443331572484820403,903989293123443331603661385682⟩,⟨(-427555093430282094332410879408),(-427555093430282094301603227595)⟩⟩
lemma root952_contains : root952.Contains (rootPhase 952) := by
  have hh := CBox.mul_contains root476_contains root476_contains (c:=root952) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def mid953 : CBox := root952
lemma mid953_contains : mid953.Contains (rootPhase 952) := root952_contains
def root953 : CBox := ⟨⟨906595704514915365319124262020,906595704514915365350497745496⟩,⟨(-422000270799799685952820594314),(-422000270799799685921804505119)⟩⟩
lemma root953_contains : root953.Contains (rootPhase 953) := by
  have hh := CBox.mul_contains mid953_contains root1_contains (c:=root953) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def root954 : CBox := ⟨⟨909167983090522376550081794980,909167983090522376581343588432⟩,⟨(-416429560097637182574065079068),(-416429560097637182543151034511)⟩⟩
lemma root954_contains : root954.Contains (rootPhase 954) := by
  have hh := CBox.mul_contains root477_contains root477_contains (c:=root954) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def mid955 : CBox := root954
lemma mid955_contains : mid955.Contains (rootPhase 954) := root954_contains
def root955 : CBox := ⟨⟨911706032005429851390473024525,911706032005429851421932170639⟩,⟨(-410843171057903942195022036606),(-410843171057903942163898933963)⟩⟩
lemma root955_contains : root955.Contains (rootPhase 955) := by
  have hh := CBox.mul_contains mid955_contains root1_contains (c:=root955) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def root956 : CBox := ⟨⟨914209755703530654621294435284,914209755703530654652300266638⟩,⟨(-405241314004989870919798094418),(-405241314004989870889121721279)⟩⟩
lemma root956_contains : root956.Contains (rootPhase 956) := by
  have hh := CBox.mul_contains root478_contains root478_contains (c:=root956) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def mid957 : CBox := root956
lemma mid957_contains : mid957.Contains (rootPhase 956) := root956_contains
def root957 : CBox := ⟨⟨916679059921042663102615909053,916679059921042663133817421576⟩,⟨(-399624199845646828555522534705),(-399624199845646828524638572487)⟩⟩
lemma root957_contains : root957.Contains (rootPhase 957) := by
  have hh := CBox.mul_contains mid957_contains root1_contains (c:=root957) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def root958 : CBox := ⟨⟨919113851690057743894671231188,919113851690057743925757675959⟩,⟨(-393992040061048108607526854035),(-393992040061048108576747613285)⟩⟩
lemma root958_contains : root958.Contains (rootPhase 958) := by
  have hh := CBox.mul_contains root479_contains root479_contains (c:=root958) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def mid959 : CBox := root958
lemma mid959_contains : mid959.Contains (rootPhase 958) := root958_contains
def root959 : CBox := ⟨⟨921514039342041943451468622595,921514039342041943482751159004⟩,⟨(-388345046698826291636421002095),(-388345046698826291605433585195)⟩⟩
lemma root959_contains : root959.Contains (rootPhase 959) := by
  have hh := CBox.mul_contains mid959_contains root1_contains (c:=root959) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def root960 : CBox := ⟨⟨923879532511286756114509592831,923879532511286756145237461415⟩,⟨(-382683432365089771739570143872),(-382683432365089771709187952854)⟩⟩
lemma root960_contains : root960.Contains (rootPhase 960) := by
  have hh := CBox.mul_contains root480_contains root480_contains (c:=root960) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def mid961 : CBox := root960
lemma mid961_contains : mid961.Contains (rootPhase 960) := root960_contains
def root961 : CBox := ⟨⟨926210242138311341960999733672,926210242138311341991921044017⟩,⟨(-377007410216418256737766464000),(-377007410216418256707178197878)⟩⟩
lemma root961_contains : root961.Contains (rootPhase 961) := by
  have hh := CBox.mul_contains mid961_contains root1_contains (c:=root961) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def root962 : CBox := ⟨⟨928506080473215565923409111501,928506080473215565954212775988⟩,⟨(-371317193951837543423065627412),(-371317193951837543392584474734)⟩⟩
lemma root962_contains : root962.Contains (rootPhase 962) := by
  have hh := CBox.mul_contains root481_contains root481_contains (c:=root962) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def mid963 : CBox := root962
lemma mid963_contains : mid963.Contains (rootPhase 962) := root962_contains
def root963 : CBox := ⟨⟨930766961078983731930993575905,930766961078983731961991066424⟩,⟨(-365612997804773870022965592705),(-365612997804773869992277812775)⟩⟩
lemma root963_contains : root963.Contains (rootPhase 963) := by
  have hh := CBox.mul_contains mid963_contains root1_contains (c:=root963) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def root964 : CBox := ⟨⟨932992798834738887697987035598,932992798834738887728526077707⟩,⟨(-359895036534988148786084699499),(-359895036534988148755847722846)⟩⟩
lemma root964_contains : root964.Contains (rootPhase 964) := by
  have hh := CBox.mul_contains root482_contains root482_contains (c:=root964) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def mid965 : CBox := root964
lemma mid965_contains : mid965.Contains (rootPhase 964) := root964_contains
def root965 : CBox := ⟨⟨935183509938947577628414411709,935183509938947577659145563965⟩,⟨(-354163525420490382368464450685),(-354163525420490382338022379681)⟩⟩
lemma root965_contains : root965.Contains (rootPhase 965) := by
  have hh := CBox.mul_contains mid965_contains root1_contains (c:=root965) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def root966 : CBox := ⟨⟨937339011912574923188143117667,937339011912574923218753275218⟩,⟨(-348418680249434568430308496005),(-348418680249434568399976150545)⟩⟩
lemma root966_contains : root966.Contains (rootPhase 966) := by
  have hh := CBox.mul_contains root483_contains root483_contains (c:=root966) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def mid967 : CBox := root966
lemma mid967_contains : mid967.Contains (rootPhase 966) := root966_contains
def root967 : CBox := ⟨⟨939459223602189911948792518774,939459223602189911979595146597⟩,⟨(-342660717311994397603870950769),(-342660717311994397573332992955)⟩⟩
lemma root967_contains : root967.Contains (rootPhase 967) := by
  have hh := CBox.mul_contains mid967_contains root1_contains (c:=root967) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def root968 : CBox := ⟨⟨941544065183020778398867280435,941544065183020778429152444992⟩,⟨(-336889853392220050700043822576),(-336889853392220050670075364762)⟩⟩
lemma root968_contains : root968.Contains (rootPhase 968) := by
  have hh := CBox.mul_contains root484_contains root484_contains (c:=root968) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def mid969 : CBox := root968
lemma mid969_contains : mid969.Contains (rootPhase 968) := root968_contains
def root969 : CBox := ⟨⟨943593458161960361481540077424,943593458161960361512015260846⟩,⟨(-331106305759876401748069730718),(-331106305759876401717897567141)⟩⟩
lemma root969_contains : root969.Contains (rootPhase 969) := by
  have hh := CBox.mul_contains mid969_contains root1_contains (c:=root969) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def root970 : CBox := ⟨⟨945607325380521325717221519858,945607325380521325747573010271⟩,⟨(-325310292162262934146764272598),(-325310292162262934116704307380)⟩⟩
lemma root970_contains : root970.Contains (rootPhase 970) := by
  have hh := CBox.mul_contains root485_contains root485_contains (c:=root970) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def mid971 : CBox := root970
lemma mid971_contains : mid971.Contains (rootPhase 970) := root970_contains
def root971 : CBox := ⟨⟨947585591017741134639543824626,947585591017741134670085668373⟩,⟨(-319502030816015677912416741417),(-319502030816015677882152587292)⟩⟩
lemma root971_contains : root971.Contains (rootPhase 971) := by
  have hh := CBox.mul_contains mid971_contains root1_contains (c:=root971) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def root972 : CBox := ⟨⟨949528180593036667182299888366,949528180593036667212377989510⟩,⟨(-313681740398891476667136826877),(-313681740398891476637327555127)⟩⟩
lemma root972_contains : root972.Contains (rootPhase 972) := by
  have hh := CBox.mul_contains root486_contains root486_contains (c:=root972) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def mid973 : CBox := root972
lemma mid973_contains : mid973.Contains (rootPhase 972) := root972_contains
def root973 : CBox := ⟨⟨951435020969008369535420419422,951435020969008369565687114083⟩,⟨(-307849640041534893692810016433),(-307849640041534893662798153431)⟩⟩
lemma root973_contains : root973.Contains (rootPhase 973) := by
  have hh := CBox.mul_contains mid973_contains root1_contains (c:=root973) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def root974 : CBox := ⟨⟨953306040354193836903023965617,953306040354193836933163650329⟩,⟨(-302005949319228067014139467672),(-302005949319228066984242349247)⟩⟩
lemma root974_contains : root974.Contains (rootPhase 974) := by
  have hh := CBox.mul_contains root487_contains root487_contains (c:=root974) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def mid975 : CBox := root974
lemma mid975_contains : mid975.Contains (rootPhase 974) := root974_contains
def root975 : CBox := ⟨⟨955141168305770721484321966018,955141168305770721514650554425⟩,⟨(-296150888243623824132551264763),(-296150888243623824102451106560)⟩⟩
lemma root975_contains : root975.Contains (rootPhase 975) := by
  have hh := CBox.mul_contains mid975_contains root1_contains (c:=root975) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def root976 : CBox := ⟨⟨956940335732208864922211615943,956940335732208864951991291195⟩,⟨(-290284677254462367646642480393),(-290284677254462367617147438509)⟩⟩
lemma root976_contains : root976.Contains (rootPhase 976) := by
  have hh := CBox.mul_contains root488_contains root488_contains (c:=root976) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def mid977 : CBox := root976
lemma mid977_contains : mid977.Contains (rootPhase 976) := root976_contains
def root977 : CBox := ⟨⟨958703474895871555360941328924,958703474895871555390907218966⟩,⟨(-284407537211271843628848844610),(-284407537211271843599152894858)⟩⟩
lemma root977_contains : root977.Contains (rootPhase 977) := by
  have hh := CBox.mul_contains mid977_contains root1_contains (c:=root977) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def root978 : CBox := ⟨⟨960430519415565811185370243295,960430519415565811215206623013⟩,⟨(-278519689385053105218316070535),(-278519689385053105188737125690)⟩⟩
lemma root978_contains : root978.Contains (rootPhase 978) := by
  have hh := CBox.mul_contains root489_contains root489_contains (c:=root978) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def mid979 : CBox := root978
lemma mid979_contains : mid979.Contains (rootPhase 978) := root978_contains
def root979 : CBox := ⟨⟨962121404269041595415820884234,962121404269041595445843763034⟩,⟨(-272621355449948984503903646672),(-272621355449948984474123380930)⟩⟩
lemma root979_contains : root979.Contains (rootPhase 979) := by
  have hh := CBox.mul_contains mid979_contains root1_contains (c:=root979) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def root980 : CBox := ⟨⟨963776065795439866672889565108,963776065795439866702444383409⟩,⟨(-266712757474898386335601851701),(-266712757474898386306279475809)⟩⟩
lemma root980_contains : root980.Contains (rootPhase 980) := by
  have hh := CBox.mul_contains root490_contains root490_contains (c:=root980) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def mid981 : CBox := root980
lemma mid981_contains : mid981.Contains (rootPhase 980) := root980_contains
def root981 : CBox := ⟨⟨965394441697689374537151228862,965394441697689374566890746968⟩,⟨(-260794117915275518290589937332),(-260794117915275518261067899497)⟩⟩
lemma root981_contains : root981.Contains (rootPhase 981) := by
  have hh := CBox.mul_contains mid981_contains root1_contains (c:=root981) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def root982 : CBox := ⟨⟨966976471044852109073568403492,966976471044852109103175134814⟩,⟨(-254865659604514571564312877854),(-254865659604514571534910318506)⟩⟩
lemma root982_contains : root982.Contains (rootPhase 982) := by
  have hh := CBox.mul_contains root491_contains root491_contains (c:=root982) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def mid983 : CBox := root982
lemma mid983_contains : mid983.Contains (rootPhase 982) := root982_contains
def root983 : CBox := ⟨⟨968522094274417316207318341540,968522094274417316237110032585⟩,⟨(-248927605745720168121103495420),(-248927605745720168091500896103)⟩⟩
lemma root983_contains : root983.Contains (rootPhase 983) := by
  have hh := CBox.mul_contains mid983_contains root1_contains (c:=root983) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def root984 : CBox := ⟨⟨970031253194543992590449177305,970031253194543992619719389003⟩,⟨(-242980179903263889958393752339),(-242980179903263889929370752809)⟩⟩
lemma root984_contains : root984.Contains (rootPhase 984) := by
  have hh := CBox.mul_contains root492_contains root492_contains (c:=root984) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def mid985 : CBox := root984
lemma mid985_contains : mid985.Contains (rootPhase 984) := root984_contains
def root985 : CBox := ⟨⟨971503890986251775523447510825,971503890986251775552900127774⟩,⟨(-237023605994367206877943387632),(-237023605994367206848722347682)⟩⟩
lemma root985_contains : root985.Contains (rootPhase 985) := by
  have hh := CBox.mul_contains mid985_contains root1_contains (c:=root985) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def root986 : CBox := ⟨⟨972939952205560145454109709717,972939952205560145483426965618⟩,⟨(-231058108280671119653371616389),(-231058108280671119624272356884)⟩⟩
lemma root986_contains : root986.Contains (rootPhase 986) := by
  have hh := CBox.mul_contains root493_contains root493_contains (c:=root986) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def mid987 : CBox := root986
lemma mid987_contains : mid987.Contains (rootPhase 986) := root986_contains
def root987 : CBox := ⟨⟨974339382785575860504993876062,974339382785575860534493771646⟩,⟨(-225083911359792836001866077415),(-225083911359792835972568434976)⟩⟩
lemma root987_contains : root987.Contains (rootPhase 987) := by
  have hh := CBox.mul_contains mid987_contains root1_contains (c:=root987) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def root988 : CBox := ⟨⟨975702130038528544446877989482,975702130038528544475905531472⟩,⟨(-219101240156869797237720462824),(-219101240156869797208883548943)⟩⟩
lemma root988_contains : root988.Contains (rootPhase 988) := by
  have hh := CBox.mul_contains root494_contains root494_contains (c:=root988) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def mid989 : CBox := root988
lemma mid989_contains : mid989.Contains (rootPhase 988) := root988_contains
def root989 : CBox := ⟨⟨977028142657754351472231778898,977028142657754351501440122998⟩,⟨(-213110319916091373977828241179),(-213110319916091373948794664651)⟩⟩
lemma root989_contains : root989.Contains (rootPhase 989) := by
  have hh := CBox.mul_contains mid989_contains root1_contains (c:=root989) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def root990 : CBox := ⟨⟨978317370719627633092648615379,978317370719627633121718366390⟩,⟨(-207111376192218549718114285400),(-207111376192218549689204888372)⟩⟩
lemma root990_contains : root990.Contains (rootPhase 990) := by
  have hh := CBox.mul_contains root495_contains root495_contains (c:=root990) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def mid991 : CBox := root990
lemma mid991_contains : mid991.Contains (rootPhase 990) := root990_contains
def root991 : CBox := ⟨⟨979569765685440534425617685684,979569765685440534454868448789⟩,⟨(-201104634842091911568530084530),(-201104634842091911539423717682)⟩⟩
lemma root991_contains : root991.Contains (rootPhase 991) := by
  have hh := CBox.mul_contains mid991_contains root1_contains (c:=root991) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def root992 : CBox := ⟨⟨980785280403230449112727300591,980785280403230449141418033424⟩,⟨(-195090322016128267858050226344),(-195090322016128267829566110949)⟩⟩
lemma root992_contains : root992.Contains (rootPhase 992) := by
  have hh := CBox.mul_contains root496_contains root496_contains (c:=root992) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def mid993 : CBox := root992
lemma mid993_contains : mid993.Contains (rootPhase 992) := root992_contains
def root993 : CBox := ⟨⟨981963869109555264059277515340,981963869109555264088146423327⟩,⟨(-189068664149806212764850646861),(-189068664149806212736171832586)⟩⟩
lemma root993_contains : root993.Contains (rootPhase 993) := by
  have hh := CBox.mul_contains mid993_contains root1_contains (c:=root993) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def root994 : CBox := ⟨⟨983105487431216327166774263457,983105487431216327195502270218⟩,⟨(-183039887955140958526312548191),(-183039887955140958497759935454)⟩⟩
lemma root994_contains : root994.Contains (rootPhase 994) := by
  have hh := CBox.mul_contains root497_contains root497_contains (c:=root994) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def mid995 : CBox := root994
lemma mid995_contains : mid995.Contains (rootPhase 994) := root994_contains
def root995 : CBox := ⟨⟨984210092386929073180231525878,984210092386929073209137892193⟩,⟨(-177004220412148756206707718339),(-177004220412148756177960135528)⟩⟩
lemma root995_contains : root995.Contains (rootPhase 995) := by
  have hh := CBox.mul_contains mid995_contains root1_contains (c:=root995) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def root996 : CBox := ⟨⟨985277642388941244760586434526,985277642388941244789017322521⟩,⟨(-170961888760301226373269660161),(-170961888760301226344984378884)⟩⟩
lemma root996_contains : root996.Contains (rootPhase 996) := by
  have hh := CBox.mul_contains root498_contains root498_contains (c:=root996) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def mid997 : CBox := root996
lemma mid997_contains : mid997.Contains (rootPhase 996) := root996_contains
def root997 : CBox := ⟨⟨986308097244598647849750319552,986308097244598647878357696631⟩,⟨(-164913120489969921427903752344),(-164913120489969921399425278168)⟩⟩
lemma root997_contains : root997.Contains (rootPhase 997) := by
  have hh := CBox.mul_contains mid997_contains root1_contains (c:=root997) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def root998 : CBox := ⟨⟨987301418157858382386313591160,987301418157858382414776888556⟩,⟨(-158858143333861441694026639965),(-158858143333861441665676684671)⟩⟩
lemma root998_contains : root998.Contains (rootPhase 998) := by
  have hh := CBox.mul_contains root499_contains root499_contains (c:=root998) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def mid999 : CBox := root998
lemma mid999_contains : mid999.Contains (rootPhase 998) := root998_contains
def root999 : CBox := ⟨⟨988257567730749491391174874185,988257567730749491419814820617⟩,⟨(-152797185258443427730065669530),(-152797185258443427701522285719)⟩⟩
lemma root999_contains : root999.Contains (rootPhase 999) := by
  have hh := CBox.mul_contains mid999_contains root1_contains (c:=root999) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def root1000 : CBox := ⟨⟨989176509964780973438290092407,989176509964780973466407579317⟩,⟨(-146730474455361751668277045409),(-146730474455361751640320393679)⟩⟩
lemma root1000_contains : root1000.Contains (rootPhase 1000) := by
  have hh := CBox.mul_contains root500_contains root500_contains (c:=root1000) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def mid1001 : CBox := root1000
lemma mid1001_contains : mid1001.Contains (rootPhase 1000) := root1000_contains
def root1001 : CBox := ⟨⟨990058210262297105492408523617,990058210262297105520700016049⟩,⟨(-140658239332849230724302824626),(-140658239332849230696154823762)⟩⟩
lemma root1001_contains : root1001.Contains (rootPhase 1001) := by
  have hh := CBox.mul_contains mid1001_contains root1_contains (c:=root1001) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def root1002 : CBox := ⟨⟨990902635427780025094784950040,990902635427780025122929936208⟩,⟨(-134580708507126186325798623446),(-134580708507126186297781253896)⟩⟩
lemma root1002_contains : root1002.Contains (rootPhase 1002) := by
  have hh := CBox.mul_contains root501_contains root501_contains (c:=root1002) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def mid1003 : CBox := root1002
lemma mid1003_contains : mid1003.Contains (rootPhase 1002) := root1002_contains
def root1003 : CBox := ⟨⟨991709753669099522846483348354,991709753669099522874802474876⟩,⟨(-128498110793793172633943293835),(-128498110793793172605734375408)⟩⟩
lemma root1003_contains : root1003.Contains (rootPhase 1003) := by
  have hh := CBox.mul_contains mid1003_contains root1_contains (c:=root1003) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def root1004 : CBox := ⟨⟨992479534598709998143412495150,992479534598709998171252908402⟩,⟨(-122410675199216198507992136760),(-122410675199216198480247064613)⟩⟩
lemma root1004_contains : root1004.Contains (rootPhase 1004) := by
  have hh := CBox.mul_contains root502_contains root502_contains (c:=root1004) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def mid1005 : CBox := root1004
lemma mid1005_contains : mid1005.Contains (rootPhase 1004) := root1004_contains
def root1005 : CBox := ⟨⟨993211949234794533091132529010,993211949234794533119145179940⟩,⟨(-116318630911904767261918886081),(-116318630911904767233984099522)⟩⟩
lemma root1005_contains : root1005.Contains (rootPhase 1005) := by
  have hh := CBox.mul_contains mid1005_contains root1_contains (c:=root1005) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def root1006 : CBox := ⟨⟨993906970002356041533501460052,993906970002356041561364483080⟩,⟨(-110222207293883058817199487007),(-110222207293883058789397566376)⟩⟩
lemma root1006_contains : root1006.Contains (rootPhase 1006) := by
  have hh := CBox.mul_contains root503_contains root503_contains (c:=root1006) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def mid1007 : CBox := root1006
lemma mid1007_contains : mid1007.Contains (rootPhase 1006) := root1006_contains
def root1007 : CBox := ⟨⟨994564570734255452105570956769,994564570734255452133606327861⟩,⟨(-104121633872054579130331546176),(-104121633872054579102339747161)⟩⟩
lemma root1007_contains : root1007.Contains (rootPhase 1007) := by
  have hh := CBox.mul_contains mid1007_contains root1_contains (c:=root1007) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def root1008 : CBox := ⟨⟨995184726672196886231549143023,995184726672196886259033893622⟩,⟨(-98017140329560602003266486275),(-98017140329560601975893270231)⟩⟩
lemma root1008_contains : root1008.Contains (rootPhase 1008) := by
  have hh := CBox.mul_contains root504_contains root504_contains (c:=root1008) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def mid1009 : CBox := root1008
lemma mid1009_contains : mid1009.Contains (rootPhase 1008) := root1008_contains
def root1009 : CBox := ⟨⟨995767414467659793969095182233,995767414467659793996749419187⟩,⟨(-91908956497132728634148411860),(-91908956497132728606587607015)⟩⟩
lemma root1009_contains : root1009.Contains (rootPhase 1009) := by
  have hh := CBox.mul_contains mid1009_contains root1_contains (c:=root1009) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def root1010 : CBox := ⟨⟨996312612182778012613873655208,996312612182778012641376081902⟩,⟨(-85797312344439890470639290158),(-85797312344439890443213204569)⟩⟩
lemma root1010_contains : root1010.Contains (rootPhase 1010) := by
  have hh := CBox.mul_contains root505_contains root505_contains (c:=root1010) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def mid1011 : CBox := root1010
lemma mid1011_contains : mid1011.Contains (rootPhase 1010) := root1010_contains
def root1011 : CBox := ⟨⟨996820299291165714959164027423,996820299291165714986836025885⟩,⟨(-79682437971430121156290526700),(-79682437971430121128676724394)⟩⟩
lemma root1011_contains : root1011.Contains (rootPhase 1011) := by
  have hh := CBox.mul_contains mid1011_contains root1_contains (c:=root1011) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def root1012 : CBox := ⟨⟨997290456678690216122344092835,997290456678690216149535202519⟩,⟨(-73564563599667423538396602930),(-73564563599667423511247028155)⟩⟩
lemma root1012_contains : root1012.Contains (rootPhase 1012) := by
  have hh := CBox.mul_contains root506_contains root506_contains (c:=root1012) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def mid1013 : CBox := root1012
lemma mid1013_contains : mid1013.Contains (rootPhase 1012) := root1012_contains
def root1013 : CBox := ⟨⟨997723066644191609835181670028,997723066644191609862540421775⟩,⟨(-67443919563664057906989712948),(-67443919563664057879654308937)⟩⟩
lemma root1013_contains : root1013.Contains (rootPhase 1013) := by
  have hh := CBox.mul_contains mid1013_contains root1_contains (c:=root1013) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def root1014 : CBox := ⟨⟨998118112900149207111839977454,998118112900149207139043862476⟩,⟨(-61320736302208577791557017884),(-61320736302208577764358478843)⟩⟩
lemma root1014_contains : root1014.Contains (rootPhase 1014) := by
  have hh := CBox.mul_contains root507_contains root507_contains (c:=root1014) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def mid1015 : CBox := root1014
lemma mid1015_contains : mid1015.Contains (rootPhase 1014) := root1014_contains
def root1015 : CBox := ⟨⟨998475580573294752195130978327,998475580573294752222502566447⟩,⟨(-55195244349689939818476649550),(-55195244349689939791092189225)⟩⟩
lemma root1015_contains : root1015.Contains (rootPhase 1015) := by
  have hh := CBox.mul_contains mid1015_contains root1_contains (c:=root1015) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def root1016 : CBox := ⟨⟨998795456205172392701575489551,998795456205172392728426405084⟩,⟨(-49067674327418014263682408640),(-49067674327418014236889154005)⟩⟩
lemma root1016_contains : root1016.Contains (rootPhase 1016) := by
  have hh := CBox.mul_contains root508_contains root508_contains (c:=root1016) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def mid1017 : CBox := root1016
lemma mid1017_contains : mid1017.Contains (rootPhase 1016) := root1016_contains
def root1017 : CBox := ⟨⟨999077727752645382875474933421,999077727752645382902490832554⟩,⟨(-42938256934940823085937943081),(-42938256934940823058960913668)⟩⟩
lemma root1017_contains : root1017.Contains (rootPhase 1017) := by
  have hh := CBox.mul_contains mid1017_contains root1_contains (c:=root1017) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def root1018 : CBox := ⟨⟨999322384588349500882963988998,999322384588349500909822764706⟩,⟨(-36807222941358832333070965347),(-36807222941358832306232707306)⟩⟩
lemma root1018_contains : root1018.Contains (rootPhase 1018) := by
  have hh := CBox.mul_contains root509_contains root509_contains (c:=root1018) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def mid1019 : CBox := root1018
lemma mid1019_contains : mid1019.Contains (rootPhase 1018) := root1018_contains
def root1019 : CBox := ⟨⟨999529417501093163066335206657,999529417501093163093359002426⟩,⟨(-30674803176636625942845648874),(-30674803176636625915823559970)⟩⟩
lemma root1019_contains : root1019.Contains (rootPhase 1019) := by
  have hh := CBox.mul_contains mid1019_contains root1_contains (c:=root1019) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def root1020 : CBox := ⟨⟨999698818696204220102610395738,999698818696204220129151178007⟩,⟨(-24541228522912288040321539995),(-24541228522912288013763884973)⟩⟩
lemma root1020_contains : root1020.Contains (rootPhase 1020) := by
  have hh := CBox.mul_contains root510_contains root510_contains (c:=root1020) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def mid1021 : CBox := root1020
lemma mid1021_contains : mid1021.Contains (rootPhase 1020) := root1020_contains
def root1021 : CBox := ⟨⟨999830581795823422002456782711,999830581795823422029160629624⟩,⟨(-18406729905804820936039050345),(-18406729905804820909299504587)⟩⟩
lemma root1021_contains : root1021.Contains (rootPhase 1021) := by
  have hh := CBox.mul_contains mid1021_contains root1_contains (c:=root1021) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def root1022 : CBox := ⟨⟨999924701839144540908432288734,999924701839144540934976024806⟩,⟨(-12271538285719926088005543191),(-12271538285719926061406824071)⟩⟩
lemma root1022_contains : root1022.Contains (rootPhase 1022) := by
  have hh := CBox.mul_contains root511_contains root511_contains (c:=root1022) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
def mid1023 : CBox := root1022
lemma mid1023_contains : mid1023.Contains (rootPhase 1022) := root1022_contains
def root1023 : CBox := ⟨⟨999981175282601142643665872561,999981175282601142670372685438⟩,⟨(-6135884649154475368323604850),(-6135884649154475341542974824)⟩⟩
lemma root1023_contains : root1023.Contains (rootPhase 1023) := by
  have hh := CBox.mul_contains mid1023_contains root1_contains (c:=root1023) (by decide +kernel)
  simpa only [← rootPhase_add] using hh
end IntegerRoots
end SharpPlanar

end OAI
