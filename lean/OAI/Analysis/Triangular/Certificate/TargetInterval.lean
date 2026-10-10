import OAI.Analysis.Triangular.Envelope.TargetEnvelope

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval
def targetZBox : RI := (RI.point 391).divNat 1000
lemma targetZBox_mem : targetZBox.Mem Z := by
  simpa [Z,targetZBox] using RI.mem_divNat (RI.mem_point 391) (by norm_num : 0<1000)
def targetRateBox (q : Fin 2) : RI := if q.val=0 then RI.point 0 else piBox.mul ((RI.point 1).divNat 5)
lemma targetRateBox_mem (q : Fin 2) : (targetRateBox q).Mem (Real.pi*(damping q-h)) := by
  fin_cases q
  · simpa [targetRateBox,damping] using ri0_mem
  · convert RI.mem_mul piBox_mem (RI.mem_divNat (RI.mem_point 1) (by norm_num : 0<5)) using 1 <;> norm_num [targetRateBox,damping,H,h]
def targetExpInput (q : Fin 2) (n : ℤ) : RI :=
  ((targetRateBox q).mul (RI.point n)).add ((RI.point (1-n)).mul targetZBox.invPos)
lemma targetExpInput_mem (q : Fin 2) (n : ℤ) :
    (targetExpInput q n).Mem (Real.pi*(damping q-h)*n+(1-n)/Z) := by
  apply RI.mem_add (RI.mem_mul (targetRateBox_mem q) (RI.mem_point n))
  rw [div_eq_mul_inv]
  exact RI.mem_mul (by simpa using RI.mem_point (1-n))
    (RI.mem_invPos targetZBox_mem (by decide +kernel))
def targetEnvBox (q : Fin 2) (qb db eb : RI) : RI :=
  ((QBox1.mul qb.invPos).mul (((RI.point 1).add targetZBox).add
    (targetZBox.mul ((targetRateBox q).sub db).abs))).mul eb
lemma targetEnvBox_mem (q : Fin 2) (n : ℤ) {qb db eb : RI}
    (hq : qb.Mem (Q n)) (hd : db.Mem (D n))
    (he : eb.Mem (Real.exp (Real.pi*(damping q-h)*n+(1-n)/Z))) (hp : 0<qb.lo) :
    (targetEnvBox q qb db eb).Mem (targetEnvelope (damping q) n) := by
  unfold targetEnvelope
  rw [div_eq_mul_inv]
  exact RI.mem_mul (RI.mem_mul (RI.mem_mul QBox1_mem (RI.mem_invPos hq hp))
    (RI.mem_add (RI.mem_add ri1_mem targetZBox_mem)
      (RI.mem_mul targetZBox_mem (RI.mem_abs (RI.mem_sub (targetRateBox_mem q) hd))))) he

def targetExpf9 : RI := ⟨371583854405964955268998186837214768409740484407723760,371583854405964955268998186837214768409740484407730647⟩
lemma targetExpf9_calc : (CI.ofReal (targetExpInput 1 9)).exp.re=targetExpf9 := by decide +kernel
lemma targetExpf9_mem : targetExpf9.Mem (Real.exp (Real.pi*(damping 1-h)*(9:ℤ)+(1-(9:ℤ))/Z)) := by
  rw [← targetExpf9_calc]
  exact ri_exp_mem (targetExpInput_mem 1 9) (by decide +kernel)
def targetEnvf9 : RI := ⟨79929592308069886255923802412064702646456854029325769,79929592308069886255923802412064702646459470384903306⟩
lemma targetEnvf9_calc : targetEnvBox 1 QBox9 DBox9 targetExpf9=targetEnvf9 := by decide +kernel
lemma targetEnvf9_mem : targetEnvf9.Mem (targetEnvelope (damping 1) 9) := by
  rw [← targetEnvf9_calc]
  apply targetEnvBox_mem 1 9 _ _ targetExpf9_mem (by decide +kernel)
  · exact QBox9_mem
  · exact DBox9_mem
def targetExpf12 : RI := ⟨1138937577370360867550942274425471604845725879364144,1138937577370360867550942274425471604845725879364176⟩
lemma targetExpf12_calc : (CI.ofReal (targetExpInput 1 12)).exp.re=targetExpf12 := by decide +kernel
lemma targetExpf12_mem : targetExpf12.Mem (Real.exp (Real.pi*(damping 1-h)*(12:ℤ)+(1-(12:ℤ))/Z)) := by
  rw [← targetExpf12_calc]
  exact ri_exp_mem (targetExpInput_mem 1 12) (by decide +kernel)
def targetEnvf12 : RI := ⟨737900748185172127488690301649742871122126409324216,737900748185172127488690301649742871122155359330918⟩
lemma targetEnvf12_calc : targetEnvBox 1 QBox12 DBox12 targetExpf12=targetEnvf12 := by decide +kernel
lemma targetEnvf12_mem : targetEnvf12.Mem (targetEnvelope (damping 1) 12) := by
  rw [← targetEnvf12_calc]
  apply targetEnvBox_mem 1 12 _ _ targetExpf12_mem (by decide +kernel)
  · exact QBox12_mem
  · exact DBox12_mem
def targetExpf13 : RI := ⟨165442703236073607826867801824880264180323233409359,165442703236073607826867801824880264180323233409366⟩
lemma targetExpf13_calc : (CI.ofReal (targetExpInput 1 13)).exp.re=targetExpf13 := by decide +kernel
lemma targetExpf13_mem : targetExpf13.Mem (Real.exp (Real.pi*(damping 1-h)*(13:ℤ)+(1-(13:ℤ))/Z)) := by
  rw [← targetExpf13_calc]
  exact ri_exp_mem (targetExpInput_mem 1 13) (by decide +kernel)
def targetEnvf13 : RI := ⟨72358775014941788641752679186749217513948768859638,72358775014941788641752679186749217513951534988133⟩
lemma targetEnvf13_calc : targetEnvBox 1 QBox13 DBox13 targetExpf13=targetEnvf13 := by decide +kernel
lemma targetEnvf13_mem : targetEnvf13.Mem (targetEnvelope (damping 1) 13) := by
  rw [← targetEnvf13_calc]
  apply targetEnvBox_mem 1 13 _ _ targetExpf13_mem (by decide +kernel)
  · exact QBox13_mem
  · exact DBox13_mem
def targetExpf16 : RI := ⟨507096606548016980840453496425200306337042956607,507096606548016980840453496425200306337042956610⟩
lemma targetExpf16_calc : (CI.ofReal (targetExpInput 1 16)).exp.re=targetExpf16 := by decide +kernel
lemma targetExpf16_mem : targetExpf16.Mem (Real.exp (Real.pi*(damping 1-h)*(16:ℤ)+(1-(16:ℤ))/Z)) := by
  rw [← targetExpf16_calc]
  exact ri_exp_mem (targetExpInput_mem 1 16) (by decide +kernel)
def targetEnvf16 : RI := ⟨14984081603111771939722335761054167345044608929,14984081603111771939722335761054167345045051454⟩
lemma targetEnvf16_calc : targetEnvBox 1 QBox16 DBox16 targetExpf16=targetEnvf16 := by decide +kernel
lemma targetEnvf16_mem : targetEnvf16.Mem (targetEnvelope (damping 1) 16) := by
  rw [← targetEnvf16_calc]
  apply targetEnvBox_mem 1 16 _ _ targetExpf16_mem (by decide +kernel)
  · exact QBox16_mem
  · exact DBox16_mem
def targetExpf19 : RI := ⟨1554296220641329958753034193228726425123681830,1554296220641329958753034193228726425123681833⟩
lemma targetExpf19_calc : (CI.ofReal (targetExpInput 1 19)).exp.re=targetExpf19 := by decide +kernel
lemma targetExpf19_mem : targetExpf19.Mem (Real.exp (Real.pi*(damping 1-h)*(19:ℤ)+(1-(19:ℤ))/Z)) := by
  rw [← targetExpf19_calc]
  exact ri_exp_mem (targetExpInput_mem 1 19) (by decide +kernel)
def targetEnvf19 : RI := ⟨42209558519464300166257608381105721464756918,42209558519464300166257608381105721464758160⟩
lemma targetEnvf19_calc : targetEnvBox 1 QBox19 DBox19 targetExpf19=targetEnvf19 := by decide +kernel
lemma targetEnvf19_mem : targetEnvf19.Mem (targetEnvelope (damping 1) 19) := by
  rw [← targetEnvf19_calc]
  apply targetEnvBox_mem 1 19 _ _ targetExpf19_mem (by decide +kernel)
  · exact QBox19_mem
  · exact DBox19_mem
def targetExpf21 : RI := ⟨32796627117040229186147692193117594753946052,32796627117040229186147692193117594753946055⟩
lemma targetExpf21_calc : (CI.ofReal (targetExpInput 1 21)).exp.re=targetExpf21 := by decide +kernel
lemma targetExpf21_mem : targetExpf21.Mem (Real.exp (Real.pi*(damping 1-h)*(21:ℤ)+(1-(21:ℤ))/Z)) := by
  rw [← targetExpf21_calc]
  exact ri_exp_mem (targetExpInput_mem 1 21) (by decide +kernel)
def targetEnvf21 : RI := ⟨490708736100926712270907069267985577233720,490708736100926712270907069267985577233735⟩
lemma targetEnvf21_calc : targetEnvBox 1 QBox21 DBox21 targetExpf21=targetEnvf21 := by decide +kernel
lemma targetEnvf21_mem : targetEnvf21.Mem (targetEnvelope (damping 1) 21) := by
  rw [← targetEnvf21_calc]
  apply targetEnvBox_mem 1 21 _ _ targetExpf21_mem (by decide +kernel)
  · exact QBox21_mem
  · exact DBox21_mem
def targetEnvTablef : Fin 6 → RI := ![targetEnvf9,targetEnvf12,targetEnvf13,targetEnvf16,targetEnvf19,targetEnvf21]
lemma targetEnvTablef_mem (i : Fin 6) : (targetEnvTablef i).Mem (targetEnvelope (damping 1) (finiteNode ⟨i.val+4,by omega⟩)) := by
  fin_cases i
  · exact targetEnvf9_mem
  · exact targetEnvf12_mem
  · exact targetEnvf13_mem
  · exact targetEnvf16_mem
  · exact targetEnvf19_mem
  · exact targetEnvf21_mem
def targetExpt36 : RI := ⟨1332093987218979628888,1332093987218979628891⟩
lemma targetExpt36_calc : (CI.ofReal (targetExpInput 0 36)).exp.re=targetExpt36 := by decide +kernel
lemma targetExpt36_mem : targetExpt36.Mem (Real.exp (Real.pi*(damping 0-h)*(36:ℤ)+(1-(36:ℤ))/Z)) := by
  rw [← targetExpt36_calc]
  exact ri_exp_mem (targetExpInput_mem 0 36) (by decide +kernel)
def targetEnvt36 : RI := ⟨983699026673584249414,983699026673584249417⟩
lemma targetEnvt36_calc : targetEnvBox 0 QBox0 DBox0 targetExpt36=targetEnvt36 := by decide +kernel
lemma targetEnvt36_mem : targetEnvt36.Mem (targetEnvelope (damping 0) 36) := by
  rw [← targetEnvt36_calc]
  apply targetEnvBox_mem 0 36 _ _ targetExpt36_mem (by decide +kernel)
  · rw [Q_emod 36]; norm_num; exact QBox0_mem
  · rw [D_emod 36]; norm_num; exact DBox0_mem
def targetExpt37 : RI := ⟨103230324563422963144,103230324563422963147⟩
lemma targetExpt37_calc : (CI.ofReal (targetExpInput 0 37)).exp.re=targetExpt37 := by decide +kernel
lemma targetExpt37_mem : targetExpt37.Mem (Real.exp (Real.pi*(damping 0-h)*(37:ℤ)+(1-(37:ℤ))/Z)) := by
  rw [← targetExpt37_calc]
  exact ri_exp_mem (targetExpInput_mem 0 37) (by decide +kernel)
def targetEnvt37 : RI := ⟨156853136021545377530,156853136021545377536⟩
lemma targetEnvt37_calc : targetEnvBox 0 QBox1 DBox1 targetExpt37=targetEnvt37 := by decide +kernel
lemma targetEnvt37_mem : targetEnvt37.Mem (targetEnvelope (damping 0) 37) := by
  rw [← targetEnvt37_calc]
  apply targetEnvBox_mem 0 37 _ _ targetExpt37_mem (by decide +kernel)
  · rw [Q_emod 37]; norm_num; exact QBox1_mem
  · rw [D_emod 37]; norm_num; exact DBox1_mem
def targetExpt39 : RI := ⟨619943545016735189,619943545016735192⟩
lemma targetExpt39_calc : (CI.ofReal (targetExpInput 0 39)).exp.re=targetExpt39 := by decide +kernel
lemma targetExpt39_mem : targetExpt39.Mem (Real.exp (Real.pi*(damping 0-h)*(39:ℤ)+(1-(39:ℤ))/Z)) := by
  rw [← targetExpt39_calc]
  exact ri_exp_mem (targetExpInput_mem 0 39) (by decide +kernel)
def targetEnvt39 : RI := ⟨2314918595180738609,2314918595180738621⟩
lemma targetEnvt39_calc : targetEnvBox 0 QBox3 DBox3 targetExpt39=targetEnvt39 := by decide +kernel
lemma targetEnvt39_mem : targetEnvt39.Mem (targetEnvelope (damping 0) 39) := by
  rw [← targetEnvt39_calc]
  apply targetEnvBox_mem 0 39 _ _ targetExpt39_mem (by decide +kernel)
  · rw [Q_emod 39]; norm_num; exact QBox3_mem
  · rw [D_emod 39]; norm_num; exact DBox3_mem
def targetExpt40 : RI := ⟨48042385880506405,48042385880506408⟩
lemma targetExpt40_calc : (CI.ofReal (targetExpInput 0 40)).exp.re=targetExpt40 := by decide +kernel
lemma targetExpt40_mem : targetExpt40.Mem (Real.exp (Real.pi*(damping 0-h)*(40:ℤ)+(1-(40:ℤ))/Z)) := by
  rw [← targetExpt40_calc]
  exact ri_exp_mem (targetExpInput_mem 0 40) (by decide +kernel)
def targetEnvt40 : RI := ⟨140114137776113727,140114137776113737⟩
lemma targetEnvt40_calc : targetEnvBox 0 QBox4 DBox4 targetExpt40=targetEnvt40 := by decide +kernel
lemma targetEnvt40_mem : targetEnvt40.Mem (targetEnvelope (damping 0) 40) := by
  rw [← targetEnvt40_calc]
  apply targetEnvBox_mem 0 40 _ _ targetExpt40_mem (by decide +kernel)
  · rw [Q_emod 40]; norm_num; exact QBox4_mem
  · rw [D_emod 40]; norm_num; exact DBox4_mem
def targetExpt43 : RI := ⟨22358457661085,22358457661088⟩
lemma targetExpt43_calc : (CI.ofReal (targetExpInput 0 43)).exp.re=targetExpt43 := by decide +kernel
lemma targetExpt43_mem : targetExpt43.Mem (Real.exp (Real.pi*(damping 0-h)*(43:ℤ)+(1-(43:ℤ))/Z)) := by
  rw [← targetExpt43_calc]
  exact ri_exp_mem (targetExpInput_mem 0 43) (by decide +kernel)
def targetEnvt43 : RI := ⟨6589731472279,6589731472281⟩
lemma targetEnvt43_calc : targetEnvBox 0 QBox7 DBox7 targetExpt43=targetEnvt43 := by decide +kernel
lemma targetEnvt43_mem : targetEnvt43.Mem (targetEnvelope (damping 0) 43) := by
  rw [← targetEnvt43_calc]
  apply targetEnvBox_mem 0 43 _ _ targetExpt43_mem (by decide +kernel)
  · rw [Q_emod 43]; norm_num; exact QBox7_mem
  · rw [D_emod 43]; norm_num; exact DBox7_mem
def targetExpt45 : RI := ⟨134272381318,134272381321⟩
lemma targetExpt45_calc : (CI.ofReal (targetExpInput 0 45)).exp.re=targetExpt45 := by decide +kernel
lemma targetExpt45_mem : targetExpt45.Mem (Real.exp (Real.pi*(damping 0-h)*(45:ℤ)+(1-(45:ℤ))/Z)) := by
  rw [← targetExpt45_calc]
  exact ri_exp_mem (targetExpInput_mem 0 45) (by decide +kernel)
def targetEnvt45 : RI := ⟨31298807609,31298807611⟩
lemma targetEnvt45_calc : targetEnvBox 0 QBox9 DBox9 targetExpt45=targetEnvt45 := by decide +kernel
lemma targetEnvt45_mem : targetEnvt45.Mem (targetEnvelope (damping 0) 45) := by
  rw [← targetEnvt45_calc]
  apply targetEnvBox_mem 0 45 _ _ targetExpt45_mem (by decide +kernel)
  · rw [Q_emod 45]; norm_num; exact QBox9_mem
  · rw [D_emod 45]; norm_num; exact DBox9_mem
def targetExpt48 : RI := ⟨62489055,62489058⟩
lemma targetExpt48_calc : (CI.ofReal (targetExpInput 0 48)).exp.re=targetExpt48 := by decide +kernel
lemma targetExpt48_mem : targetExpt48.Mem (Real.exp (Real.pi*(damping 0-h)*(48:ℤ)+(1-(48:ℤ))/Z)) := by
  rw [← targetExpt48_calc]
  exact ri_exp_mem (targetExpInput_mem 0 48) (by decide +kernel)
def targetEnvt48 : RI := ⟨35940479,35940482⟩
lemma targetEnvt48_calc : targetEnvBox 0 QBox12 DBox12 targetExpt48=targetEnvt48 := by decide +kernel
lemma targetEnvt48_mem : targetEnvt48.Mem (targetEnvelope (damping 0) 48) := by
  rw [← targetEnvt48_calc]
  apply targetEnvBox_mem 0 48 _ _ targetExpt48_mem (by decide +kernel)
  · rw [Q_emod 48]; norm_num; exact QBox12_mem
  · rw [D_emod 48]; norm_num; exact DBox12_mem
def targetExpt49 : RI := ⟨4842574,4842577⟩
lemma targetExpt49_calc : (CI.ofReal (targetExpInput 0 49)).exp.re=targetExpt49 := by decide +kernel
lemma targetExpt49_mem : targetExpt49.Mem (Real.exp (Real.pi*(damping 0-h)*(49:ℤ)+(1-(49:ℤ))/Z)) := by
  rw [← targetExpt49_calc]
  exact ri_exp_mem (targetExpInput_mem 0 49) (by decide +kernel)
def targetEnvt49 : RI := ⟨2393126,2393128⟩
lemma targetEnvt49_calc : targetEnvBox 0 QBox13 DBox13 targetExpt49=targetEnvt49 := by decide +kernel
lemma targetEnvt49_mem : targetEnvt49.Mem (targetEnvelope (damping 0) 49) := by
  rw [← targetEnvt49_calc]
  apply targetEnvBox_mem 0 49 _ _ targetExpt49_mem (by decide +kernel)
  · rw [Q_emod 49]; norm_num; exact QBox13_mem
  · rw [D_emod 49]; norm_num; exact DBox13_mem
def targetExpt52 : RI := ⟨2252,2255⟩
lemma targetExpt52_calc : (CI.ofReal (targetExpInput 0 52)).exp.re=targetExpt52 := by decide +kernel
lemma targetExpt52_mem : targetExpt52.Mem (Real.exp (Real.pi*(damping 0-h)*(52:ℤ)+(1-(52:ℤ))/Z)) := by
  rw [← targetExpt52_calc]
  exact ri_exp_mem (targetExpInput_mem 0 52) (by decide +kernel)
def targetEnvt52 : RI := ⟨67,68⟩
lemma targetEnvt52_calc : targetEnvBox 0 QBox16 DBox16 targetExpt52=targetEnvt52 := by decide +kernel
lemma targetEnvt52_mem : targetEnvt52.Mem (targetEnvelope (damping 0) 52) := by
  rw [← targetEnvt52_calc]
  apply targetEnvBox_mem 0 52 _ _ targetExpt52_mem (by decide +kernel)
  · rw [Q_emod 52]; norm_num; exact QBox16_mem
  · rw [D_emod 52]; norm_num; exact DBox16_mem
def targetExpt55 : RI := ⟨0,3⟩
lemma targetExpt55_calc : (CI.ofReal (targetExpInput 0 55)).exp.re=targetExpt55 := by decide +kernel
lemma targetExpt55_mem : targetExpt55.Mem (Real.exp (Real.pi*(damping 0-h)*(55:ℤ)+(1-(55:ℤ))/Z)) := by
  rw [← targetExpt55_calc]
  exact ri_exp_mem (targetExpInput_mem 0 55) (by decide +kernel)
def targetEnvt55 : RI := ⟨0,1⟩
lemma targetEnvt55_calc : targetEnvBox 0 QBox19 DBox19 targetExpt55=targetEnvt55 := by decide +kernel
lemma targetEnvt55_mem : targetEnvt55.Mem (targetEnvelope (damping 0) 55) := by
  rw [← targetEnvt55_calc]
  apply targetEnvBox_mem 0 55 _ _ targetExpt55_mem (by decide +kernel)
  · rw [Q_emod 55]; norm_num; exact QBox19_mem
  · rw [D_emod 55]; norm_num; exact DBox19_mem
def targetExpt57 : RI := ⟨-1,2⟩
lemma targetExpt57_calc : (CI.ofReal (targetExpInput 0 57)).exp.re=targetExpt57 := by decide +kernel
lemma targetExpt57_mem : targetExpt57.Mem (Real.exp (Real.pi*(damping 0-h)*(57:ℤ)+(1-(57:ℤ))/Z)) := by
  rw [← targetExpt57_calc]
  exact ri_exp_mem (targetExpInput_mem 0 57) (by decide +kernel)
def targetEnvt57 : RI := ⟨-1,1⟩
lemma targetEnvt57_calc : targetEnvBox 0 QBox21 DBox21 targetExpt57=targetEnvt57 := by decide +kernel
lemma targetEnvt57_mem : targetEnvt57.Mem (targetEnvelope (damping 0) 57) := by
  rw [← targetEnvt57_calc]
  apply targetEnvBox_mem 0 57 _ _ targetExpt57_mem (by decide +kernel)
  · rw [Q_emod 57]; norm_num; exact QBox21_mem
  · rw [D_emod 57]; norm_num; exact DBox21_mem
def targetExpt25 : RI := ⟨2200585237517198393137309427282307,2200585237517198393137309427282310⟩
lemma targetExpt25_calc : (CI.ofReal (targetExpInput 0 25)).exp.re=targetExpt25 := by decide +kernel
lemma targetExpt25_mem : targetExpt25.Mem (Real.exp (Real.pi*(damping 0-h)*(25:ℤ)+(1-(25:ℤ))/Z)) := by
  rw [← targetExpt25_calc]
  exact ri_exp_mem (targetExpInput_mem 0 25) (by decide +kernel)
def targetEnvt25 : RI := ⟨87131799812251848004403109991140,87131799812251848004403109991141⟩
lemma targetEnvt25_calc : targetEnvBox 0 QBox25 DBox25 targetExpt25=targetEnvt25 := by decide +kernel
lemma targetEnvt25_mem : targetEnvt25.Mem (targetEnvelope (damping 0) 25) := by
  rw [← targetEnvt25_calc]
  apply targetEnvBox_mem 0 25 _ _ targetExpt25_mem (by decide +kernel)
  · exact QBox25_mem
  · exact DBox25_mem
def targetExpt27 : RI := ⟨13215483134703708916534863346746,13215483134703708916534863346749⟩
lemma targetExpt27_calc : (CI.ofReal (targetExpInput 0 27)).exp.re=targetExpt27 := by decide +kernel
lemma targetExpt27_mem : targetExpt27.Mem (Real.exp (Real.pi*(damping 0-h)*(27:ℤ)+(1-(27:ℤ))/Z)) := by
  rw [← targetExpt27_calc]
  exact ri_exp_mem (targetExpInput_mem 0 27) (by decide +kernel)
def targetEnvt27 : RI := ⟨3697163849264717858191507441874,3697163849264717858191507441876⟩
lemma targetEnvt27_calc : targetEnvBox 0 QBox27 DBox27 targetExpt27=targetEnvt27 := by decide +kernel
lemma targetEnvt27_mem : targetEnvt27.Mem (targetEnvelope (damping 0) 27) := by
  rw [← targetEnvt27_calc]
  apply targetEnvBox_mem 0 27 _ _ targetExpt27_mem (by decide +kernel)
  · exact QBox27_mem
  · exact DBox27_mem
def targetExpt28 : RI := ⟨1024130899431529660013217530607,1024130899431529660013217530610⟩
lemma targetExpt28_calc : (CI.ofReal (targetExpInput 0 28)).exp.re=targetExpt28 := by decide +kernel
lemma targetExpt28_mem : targetExpt28.Mem (Real.exp (Real.pi*(damping 0-h)*(28:ℤ)+(1-(28:ℤ))/Z)) := by
  rw [← targetExpt28_calc]
  exact ri_exp_mem (targetExpInput_mem 0 28) (by decide +kernel)
def targetEnvt28 : RI := ⟨238163983735114174003852346393,238163983735114174003852346395⟩
lemma targetEnvt28_calc : targetEnvBox 0 QBox28 DBox28 targetExpt28=targetEnvt28 := by decide +kernel
lemma targetEnvt28_mem : targetEnvt28.Mem (targetEnvelope (damping 0) 28) := by
  rw [← targetEnvt28_calc]
  apply targetEnvBox_mem 0 28 _ _ targetExpt28_mem (by decide +kernel)
  · exact QBox28_mem
  · exact DBox28_mem
def targetExpt31 : RI := ⟨476620528616191269558476256,476620528616191269558476259⟩
lemma targetExpt31_calc : (CI.ofReal (targetExpInput 0 31)).exp.re=targetExpt31 := by decide +kernel
lemma targetExpt31_mem : targetExpt31.Mem (Real.exp (Real.pi*(damping 0-h)*(31:ℤ)+(1-(31:ℤ))/Z)) := by
  rw [← targetExpt31_calc]
  exact ri_exp_mem (targetExpInput_mem 0 31) (by decide +kernel)
def targetEnvt31 : RI := ⟨6138805489362733871230068,6138805489362733871230069⟩
lemma targetEnvt31_calc : targetEnvBox 0 QBox31 DBox31 targetExpt31=targetEnvt31 := by decide +kernel
lemma targetEnvt31_mem : targetEnvt31.Mem (targetEnvelope (damping 0) 31) := by
  rw [← targetEnvt31_calc]
  apply targetEnvBox_mem 0 31 _ _ targetExpt31_mem (by decide +kernel)
  · exact QBox31_mem
  · exact DBox31_mem
def targetEnvTablet : Fin 15 → RI := ![targetEnvt36,targetEnvt37,targetEnvt39,targetEnvt40,targetEnvt43,targetEnvt45,targetEnvt48,targetEnvt49,targetEnvt52,targetEnvt55,targetEnvt57,targetEnvt25,targetEnvt27,targetEnvt28,targetEnvt31]
lemma targetEnvTablet_mem (i : Fin 15) : (targetEnvTablet i).Mem (targetEnvelope (damping 0) (tailBase i)) := by
  fin_cases i
  · exact targetEnvt36_mem
  · exact targetEnvt37_mem
  · exact targetEnvt39_mem
  · exact targetEnvt40_mem
  · exact targetEnvt43_mem
  · exact targetEnvt45_mem
  · exact targetEnvt48_mem
  · exact targetEnvt49_mem
  · exact targetEnvt52_mem
  · exact targetEnvt55_mem
  · exact targetEnvt57_mem
  · exact targetEnvt25_mem
  · exact targetEnvt27_mem
  · exact targetEnvt28_mem
  · exact targetEnvt31_mem
def finiteTargetBox : RI := ⟨80739866858051870539391411993765471239633981294109190,80739866858051870539391411993765471239636629366265706⟩
lemma finiteTargetBox_calc : RI.sum targetEnvTablef=finiteTargetBox := by decide +kernel
lemma finiteTargetEnvelope_bound : finiteTargetEnvelope < (81/10^9:ℝ) := by
  have hh := RI.mem_sum targetEnvTablef_mem
  rw [finiteTargetBox_calc] at hh
  have hb := ri_mem_lt hh 81 (10^9) (by norm_num) (by decide +kernel)
  simpa [finiteTargetEnvelope,tailTargetEnvelope,damping,div_eq_mul_inv,show (10:ℝ)^9=1000000000 by norm_num,show (10:ℝ)^30=1000000000000000000000000000000 by norm_num] using hb
def targetRatioBox : RI := ⟨103230324563422963144,103230324563422963147⟩
lemma targetRatioBox_calc : (CI.ofReal ((RI.point (-36)).mul targetZBox.invPos)).exp.re=targetRatioBox := by decide +kernel
lemma targetRatioBox_mem : targetRatioBox.Mem (Real.exp (-36/Z)) := by
  rw [←targetRatioBox_calc]
  apply ri_exp_mem
  · rw [div_eq_mul_inv]
    exact RI.mem_mul (by simpa using RI.mem_point (-36)) (RI.mem_invPos targetZBox_mem (by decide +kernel))
  · decide +kernel
def tailTargetBox : RI := ⟨91067133785200176601381496102314,91067133785200176601381496102365⟩
lemma tailTargetBox_calc : (RI.sum targetEnvTablet).mul (((RI.point 1).sub targetRatioBox).invPos)=tailTargetBox := by decide +kernel
lemma tailTargetEnvelope_bound : tailTargetEnvelope < (92/10^30:ℝ) := by
  have hh := RI.mem_mul (RI.mem_sum targetEnvTablet_mem)
    (RI.mem_invPos (RI.mem_sub ri1_mem targetRatioBox_mem) (by decide +kernel))
  rw [tailTargetBox_calc] at hh
  have hb := ri_mem_lt hh 92 (10^30) (by norm_num) (by decide +kernel)
  simpa [finiteTargetEnvelope,tailTargetEnvelope,damping,div_eq_mul_inv,show (10:ℝ)^9=1000000000 by norm_num,show (10:ℝ)^30=1000000000000000000000000000000 by norm_num] using hb
end AtomicTriangular.FiniteCertificate
end

end OAI
