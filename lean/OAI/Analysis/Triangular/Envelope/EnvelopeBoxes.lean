import OAI.Analysis.Triangular.Envelope.Analytic

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.Construction
open Complex

def frequencyDistance (l : Fin 31) : ℕ := Int.natAbs ((l.val:ℤ)-15)
def fullTailW (i : Fin 15) (d : Fin 2) : ℝ :=
  if d.val=0 then Real.pi^2/18^2 * ∑ l : Fin 31,
    if i.val < frequencyDistance l then
      ((frequencyDistance l:ℝ)-i.val-1/2)*‖fourierCoeff l‖ else 0
  else Real.pi/18 * ∑ l : Fin 31,
    if i.val < frequencyDistance l then ‖fourierCoeff l‖ else 0

def tailBase (a : Fin 15) : ℤ := residue a + if residue a < 25 then 36 else 0
lemma tailBase_mod (a : Fin 15) : tailBase a % 36 = residue a := by
  fin_cases a <;> norm_num [tailBase,residue]
lemma tailBase_pos (a : Fin 15) : 25 ≤ tailBase a := by
  fin_cases a <;> norm_num [tailBase,residue]
lemma tailBase_lt (a : Fin 15) : tailBase a < 61 := by
  fin_cases a <;> norm_num [tailBase,residue]

def normJetEnvelope (k v : ℝ) (n : ℤ) (t : ℝ) : ℝ :=
  (1+|D n|+‖I*Real.pi*zeta k v t‖)*‖lambda k t‖*(Q n)⁻¹ *
    Real.exp (-frequencyDecay k v t*n)
lemma normJetEnvelope_eq {k : ℝ} (hk : 0<k) (v : ℝ) (n : ℤ) (t : ℝ) :
    normJetEnvelope k v n t = jetEnvelope k v n t := by
  rw [normJetEnvelope,norm_wavePhase hk,norm_lambda hk]
  simp only [jetEnvelope,frequencyDecay,div_eq_mul_inv,neg_mul]
end AtomicTriangular.Construction
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval Complex
lemma ri0_mem : (RI.point 0).Mem (0:ℝ) := by simpa using RI.mem_point 0
lemma ri1_mem : (RI.point 1).Mem (1:ℝ) := by simpa using RI.mem_point 1
lemma ri2_mem : (RI.point 2).Mem (2:ℝ) := by simpa using RI.mem_point 2
lemma ri18_mem : (RI.point 18).Mem (18:ℝ) := by simpa using RI.mem_point 18
lemma ri_exp_mem {a : RI} {x : ℝ} (hx : a.Mem x)
    (h : (CI.ofReal a).normSq.hi ≤ scale*1024^2) :
    (CI.ofReal a).exp.re.Mem (Real.exp x) := by
  have hh := (CI.mem_exp_checked (CI.mem_ofReal hx) h).1
  simpa only [← Complex.ofReal_exp,Complex.ofReal_re] using hh

def fullTailWBox (pn : Fin 31 → RI) (i : Fin 15) (d : Fin 2) : RI :=
  if d.val=0 then ((piBox.pow 2).divNat (18^2)).mul (RI.sum (fun l : Fin 31 =>
    if i.val < frequencyDistance l then
      (((RI.point ((frequencyDistance l:ℤ)-i.val)).sub ((RI.point 1).divNat 2)).mul (pn l)) else RI.point 0))
  else (piBox.divNat 18).mul (RI.sum (fun l : Fin 31 =>
    if i.val < frequencyDistance l then pn l else RI.point 0))
lemma fullTailWBox_mem (pn : Fin 31 → RI) (hp : ∀ l, (pn l).Mem ‖fourierCoeff l‖)
    (i : Fin 15) (d : Fin 2) : (fullTailWBox pn i d).Mem (fullTailW i d) := by
  unfold fullTailWBox fullTailW
  split_ifs with hd
  · apply RI.mem_mul (by norm_num at *; simpa using RI.mem_divNat (RI.mem_pow piBox_mem 2) (by norm_num : 0<(18^2:ℕ)))
    apply RI.mem_sum
    intro l
    split_ifs
    · apply RI.mem_mul _ (hp l)
      apply RI.mem_sub
      · simpa using RI.mem_point ((frequencyDistance l:ℤ)-i.val)
      · simpa using RI.mem_divNat ri1_mem (by norm_num : 0<(2:ℕ))
    · exact ri0_mem
  · apply RI.mem_mul (by simpa using RI.mem_divNat piBox_mem (by norm_num : 0<(18:ℕ)))
    apply RI.mem_sum
    intro l
    split_ifs
    · exact hp l
    · exact ri0_mem

def decayBox (q v : Fin 2) (j : Fin 31) : RI := (wavePhaseBox q v j).re.neg
lemma decayBox_mem (q v : Fin 2) (j : Fin 31) :
    (decayBox q v j).Mem (frequencyDecay (damping q) (damping v) (frequency j)) := by
  have hh := RI.mem_neg (wavePhaseBox_mem q v j).1
  convert hh using 1
  · rfl
  · rw [wavePhase_re]
    unfold frequencyDecay
    ring

def decayExpBox (q v : Fin 2) (n : ℤ) (j : Fin 31) : RI :=
  (CI.ofReal ((decayBox q v j).neg.mul (RI.point n))).exp.re
lemma decayExpBox_mem (q v : Fin 2) (n : ℤ) (j : Fin 31)
    (hh : (CI.ofReal ((decayBox q v j).neg.mul (RI.point n))).normSq.hi ≤ scale*1024^2) :
    (decayExpBox q v n j).Mem (Real.exp (-frequencyDecay (damping q) (damping v) (frequency j)*n)) :=
  ri_exp_mem (RI.mem_mul (RI.mem_neg (decayBox_mem q v j)) (RI.mem_point n)) hh

def psiBox (_q _v : Fin 2) (_n : ℤ) (_j : Fin 31) (qb db lell dnorm ex : RI) : RI :=
  ((((RI.point 1).add db.abs).add dnorm).mul lell).mul qb.invPos |>.mul ex
lemma psiBox_mem (q v : Fin 2) (n : ℤ) (j : Fin 31) {qb db lell dnorm ex : RI}
    (hq : qb.Mem (Q n)) (hd : db.Mem (D n))
    (hl : lell.Mem ‖lambda (damping q) (frequency j)‖)
    (hn : dnorm.Mem ‖I*Real.pi*zeta (damping q) (damping v) (frequency j)‖)
    (he : ex.Mem (Real.exp (-frequencyDecay (damping q) (damping v) (frequency j)*n)))
    (hqp : 0<qb.lo) :
    (psiBox q v n j qb db lell dnorm ex).Mem (normJetEnvelope (damping q) (damping v) n (frequency j)) := by
  exact RI.mem_mul (RI.mem_mul (RI.mem_mul (RI.mem_add (RI.mem_add ri1_mem (RI.mem_abs hd)) hn) hl)
    (RI.mem_invPos hq hqp)) he
end AtomicTriangular.FiniteCertificate
end

end OAI
