import OAI.Analysis.Triangular.Certificate.Inverse

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval Matrix
def etaPiBox : RI := piBox.mul ((RI.point 1).divNat 5)
lemma etaPiBox_mem : etaPiBox.Mem (Real.pi*eta) := by
  apply RI.mem_mul piBox_mem
  simpa [eta] using RI.mem_divNat (RI.mem_point 1) (by norm_num : 0<(5:ℕ))
def targetExp1 : CI := ⟨⟨1874456087585338350570292911831758804106207970527136794947232,1874456087585338350570292911831758804106207970527140544080552⟩,⟨-89486,127712⟩⟩
lemma targetExp1_calc : (CI.ofReal (etaPiBox.mul (RI.point 1))).exp = targetExp1 := by decide +kernel
lemma targetExp1_mem : targetExp1.Mem (Complex.exp ((Real.pi*eta*(1:ℤ):ℝ):ℂ)) := by
  rw [← targetExp1_calc]
  apply CI.mem_exp_checked
  · exact CI.mem_ofReal (RI.mem_mul etaPiBox_mem (RI.mem_point 1))
  · decide +kernel
def targetExp3 : CI := ⟨⟨6586061962694724858363079230007804318951962476704132881322785,6586061962694724858363079230007804318951962476704172398460991⟩,⟨-299830,445690⟩⟩
lemma targetExp3_calc : (CI.ofReal (etaPiBox.mul (RI.point 3))).exp = targetExp3 := by decide +kernel
lemma targetExp3_mem : targetExp3.Mem (Complex.exp ((Real.pi*eta*(3:ℤ):ℝ):ℂ)) := by
  rw [← targetExp3_calc]
  apply CI.mem_exp_checked
  · exact CI.mem_ofReal (RI.mem_mul etaPiBox_mem (RI.mem_point 3))
  · decide +kernel
def targetExp4 : CI := ⟨⟨12345283939187368579546362975259193426256726581361584530677933,12345283939187368579546362975259193426256726581361683294398213⟩,⟨-559982,834380⟩⟩
lemma targetExp4_calc : (CI.ofReal (etaPiBox.mul (RI.point 4))).exp = targetExp4 := by decide +kernel
lemma targetExp4_mem : targetExp4.Mem (Complex.exp ((Real.pi*eta*(4:ℤ):ℝ):ℂ)) := by
  rw [← targetExp4_calc]
  apply CI.mem_exp_checked
  · exact CI.mem_ofReal (RI.mem_mul etaPiBox_mem (RI.mem_point 4))
  · decide +kernel
def targetExp7 : CI := ⟨⟨81306804970548025028728213865486592780875124829090734179774898,81306804970548025028728213865486592780875124829091872484574647⟩,⟨-3590186,5502878⟩⟩
lemma targetExp7_calc : (CI.ofReal (etaPiBox.mul (RI.point 7))).exp = targetExp7 := by decide +kernel
lemma targetExp7_mem : targetExp7.Mem (Complex.exp ((Real.pi*eta*(7:ℤ):ℝ):ℂ)) := by
  rw [← targetExp7_calc]
  apply CI.mem_exp_checked
  · exact CI.mem_ofReal (RI.mem_mul etaPiBox_mem (RI.mem_point 7))
  · decide +kernel
def targetExp9 : CI := ⟨⟨285678421101121373296910627054045027465449762627940480024201346,285678421101121373296910627054045027465449762627945622269619008⟩,⟨-12198192,19184204⟩⟩
lemma targetExp9_calc : (CI.ofReal (etaPiBox.mul (RI.point 9))).exp = targetExp9 := by decide +kernel
lemma targetExp9_mem : targetExp9.Mem (Complex.exp ((Real.pi*eta*(9:ℤ):ℝ):ℂ)) := by
  rw [← targetExp9_calc]
  apply CI.mem_exp_checked
  · exact CI.mem_ofReal (RI.mem_mul etaPiBox_mem (RI.mem_point 9))
  · decide +kernel
def targetExp12 : CI := ⟨⟨1881495782776781532852850263821915726713407411393103994834360489,1881495782776781532852850263821915726713407411393149150951454626⟩,⟨-79274714,125984300⟩⟩
lemma targetExp12_calc : (CI.ofReal (etaPiBox.mul (RI.point 12))).exp = targetExp12 := by decide +kernel
lemma targetExp12_mem : targetExp12.Mem (Complex.exp ((Real.pi*eta*(12:ℤ):ℝ):ℂ)) := by
  rw [← targetExp12_calc]
  apply CI.mem_exp_checked
  · exact CI.mem_ofReal (RI.mem_mul etaPiBox_mem (RI.mem_point 12))
  · decide +kernel
def targetExp13 : CI := ⟨⟨3526781223792079544620739081630049069956543439091374085403532668,3526781223792079544620739081630049069956543439091465782125133725⟩,⟨-147616118,236466238⟩⟩
lemma targetExp13_calc : (CI.ofReal (etaPiBox.mul (RI.point 13))).exp = targetExp13 := by decide +kernel
lemma targetExp13_mem : targetExp13.Mem (Complex.exp ((Real.pi*eta*(13:ℤ):ℝ):ℂ)) := by
  rw [← targetExp13_calc]
  apply CI.mem_exp_checked
  · exact CI.mem_ofReal (RI.mem_mul etaPiBox_mem (RI.mem_point 13))
  · decide +kernel
def targetExp16 : CI := ⟨⟨23227599668762967071881451076152236804878668516890355990185412686,23227599668762967071881451076152236804878668516891099276032739152⟩,⟨-963281130,1545340506⟩⟩
lemma targetExp16_calc : (CI.ofReal (etaPiBox.mul (RI.point 16))).exp = targetExp16 := by decide +kernel
lemma targetExp16_mem : targetExp16.Mem (Complex.exp ((Real.pi*eta*(16:ℤ):ℝ):ℂ)) := by
  rw [← targetExp16_calc]
  apply CI.mem_exp_checked
  · exact CI.mem_ofReal (RI.mem_mul etaPiBox_mem (RI.mem_point 16))
  · decide +kernel
def targetExp19 : CI := ⟨⟨152978410663140367916372603043345717766819220723182442689619188462,152978410663140367916372603043345717766819220723188255886496314568⟩,⟨-6149562064,10174537158⟩⟩
lemma targetExp19_calc : (CI.ofReal (etaPiBox.mul (RI.point 19))).exp = targetExp19 := by decide +kernel
lemma targetExp19_mem : targetExp19.Mem (Complex.exp ((Real.pi*eta*(19:ℤ):ℝ):ℂ)) := by
  rw [← targetExp19_calc]
  apply CI.mem_exp_checked
  · exact CI.mem_ofReal (RI.mem_mul etaPiBox_mem (RI.mem_point 19))
  · decide +kernel
def targetExp21 : CI := ⟨⟨537502744532089381174095882504998632861298023555570017400851929660,537502744532089381174095882504998632861298023555592592579196475004⟩,⟨-21799573834,35672662814⟩⟩
lemma targetExp21_calc : (CI.ofReal (etaPiBox.mul (RI.point 21))).exp = targetExp21 := by decide +kernel
lemma targetExp21_mem : targetExp21.Mem (Complex.exp ((Real.pi*eta*(21:ℤ):ℝ):ℂ)) := by
  rw [← targetExp21_calc]
  apply CI.mem_exp_checked
  · exact CI.mem_ofReal (RI.mem_mul etaPiBox_mem (RI.mem_point 21))
  · decide +kernel
def targetExpTable : Fin 10 → CI := ![targetExp1,targetExp3,targetExp4,targetExp7,targetExp9,targetExp12,targetExp13,targetExp16,targetExp19,targetExp21]
lemma targetExpTable_mem (n : Fin 10) : (targetExpTable n).Mem (Complex.exp ((Real.pi*eta*(finiteNode n):ℝ):ℂ)) := by
  fin_cases n
  · exact targetExp1_mem
  · exact targetExp3_mem
  · exact targetExp4_mem
  · exact targetExp7_mem
  · exact targetExp9_mem
  · exact targetExp12_mem
  · exact targetExp13_mem
  · exact targetExp16_mem
  · exact targetExp19_mem
  · exact targetExp21_mem
def targetCoefficientBox (n : Fin 10) : RI := (QBox1.mul (QTable n).invPos).mul (targetExpTable n).re
lemma targetCoefficientBox_mem (n : Fin 10) : (targetCoefficientBox n).Mem (targetCoefficient n) := by
  have he : ((Complex.exp ((Real.pi*eta*(finiteNode n):ℝ):ℂ))).re = Real.exp (Real.pi*eta*(finiteNode n)) := by rw [Complex.exp_ofReal_re]
  have hq : ∀ n : Fin 10, 0 < (QTable n).lo := by decide +kernel
  unfold targetCoefficient
  rw [div_eq_mul_inv]
  apply RI.mem_mul (RI.mem_mul QBox1_mem (RI.mem_invPos (QTable_mem n) (hq n)))
  simpa only [he] using (targetExpTable_mem n).1

def YfBox (i : Fin 20) (j : Fin 8) : RI :=
  if i.val<8 then (targetCoefficientBox ⟨i.val/2,by omega⟩).mul
    (if i.val%2=0 then (if j.val=i.val then RI.point 1 else RI.point 0)
     else (if j.val=i.val then RI.point (-1) else if j.val=i.val-1 then etaPiBox.sub (DTable ⟨i.val/2,by omega⟩) else RI.point 0))
  else RI.point 0
lemma YfBox_mem (i : Fin 20) (j : Fin 8) : (YfBox i j).Mem (Yf i j) := by
  unfold YfBox Yf
  split_ifs
  all_goals first
    | apply RI.mem_mul (targetCoefficientBox_mem _); first
        | simpa using RI.mem_point 1
        | simpa using RI.mem_point (-1)
        | simpa using RI.mem_point 0
        | exact RI.mem_sub etaPiBox_mem (DTable_mem _)
    | simpa using RI.mem_point 0

def gammaBox (side : Fin 2) (i : Fin 3) (j : Fin 8) : RI :=
  if j.val=1 then (if i.val=0 then (RI.point 11).divNat 25 else if i.val=1 then RI.point 0 else if side.val=0 then ((RI.point 3).divNat 500).neg else (RI.point 3).divNat 500) else RI.point 0
lemma gammaBox_mem (side : Fin 2) (i : Fin 3) (j : Fin 8) : (gammaBox side i j).Mem (gamma side i j) := by
  unfold gammaBox gamma
  split_ifs
  all_goals first
    | simpa using RI.mem_point 0
    | simpa using RI.mem_divNat (RI.mem_point 11) (by norm_num : 0<(25:ℕ))
    | simpa using RI.mem_neg (RI.mem_divNat (RI.mem_point 3) (by norm_num : 0<(500:ℕ)))
    | simpa using RI.mem_divNat (RI.mem_point 3) (by norm_num : 0<(500:ℕ))

def rhsPlusBox (i : Fin 20) (j : Fin 8) : RI :=
  (YfBox i j).add (matrixMul R0Box (fun k j => (gammaBox 1 k j).add (gammaBox 0 k j)) i j)
def rhsMinusBox (i : Fin 20) (j : Fin 8) : RI :=
  (YfBox i j).add (matrixMul R0Box (fun k j => (gammaBox 1 k j).sub (gammaBox 0 k j)) i j)
lemma rhsPlusBox_mem (i : Fin 20) (j : Fin 8) :
    (rhsPlusBox i j).Mem ((Yf+Construction.R0*(gamma 1+gamma 0)) i j) :=
  RI.mem_add (YfBox_mem i j) (matrixMul_mem R0Box_mem (fun k j => RI.mem_add (gammaBox_mem 1 k j) (gammaBox_mem 0 k j)) i j)
lemma rhsMinusBox_mem (i : Fin 20) (j : Fin 8) :
    (rhsMinusBox i j).Mem ((Yf+Construction.R0*(gamma 1-gamma 0)) i j) :=
  RI.mem_add (YfBox_mem i j) (matrixMul_mem R0Box_mem (fun k j => RI.mem_sub (gammaBox_mem 1 k j) (gammaBox_mem 0 k j)) i j)
def UplusBox (i : Fin 20) (j : Fin 8) : RI := matrixMul minusInverseBox rhsPlusBox i j
def UminusBox (i : Fin 20) (j : Fin 8) : RI := matrixMul plusInverseBox rhsMinusBox i j
lemma UplusBox_mem (i : Fin 20) (j : Fin 8) : (UplusBox i j).Mem (Uplus i j) :=
  matrixMul_mem minusInverseBox_mem rhsPlusBox_mem i j
lemma UminusBox_mem (i : Fin 20) (j : Fin 8) : (UminusBox i j).Mem (Uminus i j) :=
  matrixMul_mem plusInverseBox_mem rhsMinusBox_mem i j

def finiteSolutionBox (side : Fin 2) (i : Fin 20) (j : Fin 8) : RI :=
  if side.val=0 then ((UplusBox i j).add (UminusBox i j)).divNat 2 else ((UplusBox i j).sub (UminusBox i j)).divNat 2
lemma finiteSolutionBox_mem (side : Fin 2) (i : Fin 20) (j : Fin 8) :
    (finiteSolutionBox side i j).Mem (finiteSolution side i j) := by
  unfold finiteSolution finiteSolutionBox
  split_ifs
  · simpa only [Matrix.smul_apply, Matrix.add_apply, Nat.cast_ofNat, smul_eq_mul, one_div, div_eq_mul_inv, mul_comm, one_mul] using
      RI.mem_divNat (RI.mem_add (UplusBox_mem i j) (UminusBox_mem i j)) (by norm_num : 0<(2:ℕ))
  · simpa only [Matrix.smul_apply, Matrix.sub_apply, Nat.cast_ofNat, smul_eq_mul, one_div, div_eq_mul_inv, mul_comm, one_mul] using
      RI.mem_divNat (RI.mem_sub (UplusBox_mem i j) (UminusBox_mem i j)) (by norm_num : 0<(2:ℕ))

def AcoefficientBox (side : Fin 2) (i : Fin 23) (j : Fin 8) : RI :=
  if hi : i.val<2 then gammaBox side ⟨i.val,by omega⟩ j
  else if h22 : i.val=22 then gammaBox side 2 j
  else finiteSolutionBox side ⟨i.val-2,by omega⟩ j
lemma AcoefficientBox_mem (side : Fin 2) (i : Fin 23) (j : Fin 8) :
    (AcoefficientBox side i j).Mem (Acoefficient side i j) := by
  unfold AcoefficientBox Acoefficient
  split_ifs
  · exact gammaBox_mem _ _ _
  · exact gammaBox_mem _ _ _
  · exact finiteSolutionBox_mem _ _ _

end AtomicTriangular.FiniteCertificate
end

end OAI
