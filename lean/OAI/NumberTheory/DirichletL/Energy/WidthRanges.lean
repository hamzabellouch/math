import OAI.NumberTheory.DirichletL.Energy.WidthSchedule
import OAI.NumberTheory.DirichletL.Energy.Profiles
import OAI.NumberTheory.DirichletL.Moments.FirstSecondInputGates

namespace OAI

noncomputable section

namespace SevenEighths.CenteredMomentEnergyWidthRanges
open CenteredMomentEnergyProfiles CenteredMomentEnergyWidthSchedule

def step (M B L:ℝ):ℝ:=4*(L+M+B+4)
def range (M B L:ℝ):ℕ→ℝ
  | 0=>max 1 L
  | n+1=>step M B (range M B L n)
def sourceCap (M B L:ℝ)(n:ℕ):ℝ:=10*(range M B L n+M+B+1)
def finalSourceCap (M B L ε:ℝ):ℝ:=sourceCap M B L (count M ε)
def fineMesh (M B L κ ε:ℝ):ℝ:=mesh M (finalSourceCap M B L ε) κ ε

lemma range_nonneg (M B L:ℝ)(hM:0≤M)(hB:0≤B)(n:ℕ):0≤range M B L n:=by
  induction n with
  | zero=>exact zero_le_one.trans (le_max_left _ _)
  | succ n ih=>simp only [range,step];positivity

lemma range_mono (M B L:ℝ)(hM:0≤M)(hB:0≤B):Monotone (range M B L):=by
  apply monotone_nat_of_le_succ
  intro n
  have hh:=range_nonneg M B L hM hB n
  simp only [range,step]
  linarith

lemma range_original (M B L:ℝ)(hM:0≤M)(hB:0≤B)(n:ℕ):L≤range M B L n:=by
  exact (le_max_right (1:ℝ) L).trans (range_mono M B L hM hB (Nat.zero_le n))

lemma step_admits (M B L rho d e:ℝ)(hM:0≤M)(hB:0≤B)(hL:0≤L)
    (hrho:rho≤1)(hd:d≤1)(he:e≤1):
    L≤step M B L ∧ M+B+rho/100+1≤step M B L ∧
    max L (M+B+2*d)+1≤step M B L ∧
    2*L+e≤step M B L ∧
    2*(max L (M+B+2*d)+1)+e≤step M B L:=by
  have hmax:max L (M+B+2*d)≤L+M+B+2:=by
    apply max_le <;> linarith
  unfold step
  constructor
  · linarith
  constructor
  · linarith
  constructor
  · linarith
  constructor <;> linarith

lemma range_envelope (M B L:ℝ)(hM:0≤M)(hB:0≤B)(n:ℕ):
    range M B L n≤(8:ℝ)^n*(max 1 L+M+B+4):=by
  induction n with
  | zero=>simp only [range,pow_zero,one_mul];linarith
  | succ n ih=>
    have hp:1≤(8:ℝ)^n:=one_le_pow₀ (by norm_num)
    have ha:0≤max 1 L:=zero_le_one.trans (le_max_left _ _)
    have hm:M+B+4≤(8:ℝ)^n*(max 1 L+M+B+4):=by
      have hh:=mul_le_mul_of_nonneg_right hp (show 0≤max 1 L+M+B+4 by positivity)
      simp only [one_mul] at hh
      linarith
    simp only [range,step,pow_succ]
    nlinarith

lemma ready_exponent_le (M B L A D P q e xi:ℝ)(n:ℕ)
    (hM:0≤M)(hB:0≤B)
    (hA:A≤2*range M B L n+M+1)(hD:D≤1)(hP:P≤B)
    (hq:q≤4*range M B L n+3*M+4)(he:e≤1)(hxi:xi≤1):
    CenteredMomentFirstSecondInputGates.exponent A D P q e xi≤sourceCap M B L n:=by
  have hr:=range_nonneg M B L hM hB n
  unfold CenteredMomentFirstSecondInputGates.exponent sourceCap
  apply max_le
  · linarith
  apply max_le
  · linarith
  apply max_le <;> linarith

lemma sourceCap_nonneg (M B L:ℝ)(hM:0≤M)(hB:0≤B)(n:ℕ):0≤sourceCap M B L n:=by
  have hr:=range_nonneg M B L hM hB n
  unfold sourceCap
  positivity

lemma fineMesh_pos (M B L κ ε:ℝ)(hM:0≤M)(hB:0≤B)(hκ:0≤κ)(hε:0<ε):
    0<fineMesh M B L κ ε:=by
  exact (bounds M (finalSourceCap M B L ε) κ ε hM
    (sourceCap_nonneg M B L hM hB _) hκ hε).2.2.2.2.1

lemma support_step (a b:ℝ)(ha:0<a)(n:ℕ):
    0<lower a b (n+1) ∧ lower a b (n+1)=lower a b n/max 1 b:=
  ⟨lower_pos a b ha _,rfl⟩

end SevenEighths.CenteredMomentEnergyWidthRanges

end

end OAI
