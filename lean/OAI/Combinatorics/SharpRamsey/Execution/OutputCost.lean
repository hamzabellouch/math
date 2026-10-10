import Mathlib
import OAI.Combinatorics.SharpRamsey.Marking.RootCost

namespace OAI

section
namespace SharpLogRamsey.ActualPivot
open Finset Real ExecutedPotential TreeDecoder
open scoped Classical
noncomputable section
variable {K V : Type} [Field K] [Finite K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V]
  [Fintype (Projectivization K V)] [Fintype (Projectivization K (Module.Dual K V))]
  [Fintype (Projectivization K (Module.Dual K (Module.Dual K V))) ]

omit [FiniteDimensional K V] in
lemma reciprocal_cost_envelope {d w h m : ℕ} {b P H σ C : ℝ}
    (hdim : Module.finrank K V=d+3) (hlog : log (Nat.card K:ℝ)=σ)
    (hσ : 1≤σ) (hw : 1≤w) (hh : 1≤h)
    (hH : 0≤H) (hP : 4≤P) (hbP : b+log 1000000≤P)
    (hwlog : log ((w:ℝ)+1)≤C*σ) (hmlog : log ((m:ℝ)+1)≤C*σ) :
    reciprocalOutputCost (K:=K) (V:=V) (I:=Fin w) (d:=d) (b:=b) (P:=P) (H:=H) w h m ≤
      (2*(H+22)*(2*((d:ℝ)+4)+1003))*(Nat.card K:ℝ)*P*(h:ℝ)*(σ+(w:ℝ)*P)+
      (3+2*C+2*((d:ℝ)+4))*(w:ℝ)*σ := by
  have hσ0 : 0≤σ:=by linarith
  have hw1 : (1:ℝ)≤w:=by exact_mod_cast hw
  have hh1 : (1:ℝ)≤h:=by exact_mod_cast hh
  have hP0 : 0≤P:=by linarith
  have hhead:=headerCost_linear hdim (by rwa [hlog])
  have hpot:=root_potential_linear hdim (by rwa [hlog])
  rw [hlog] at hhead hpot
  have hlog2 : log (2:ℝ)≤1 := by
    have hh:=log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2)
    linarith
  have hshape : ((2*w+1:ℕ):ℝ)*log 2≤3*(w:ℝ)*σ := by
    push_cast
    calc
      _ ≤ (2*(w:ℝ)+1)*1 := mul_le_mul_of_nonneg_left hlog2 (by positivity)
      _ ≤ 3*(w:ℝ) := by linarith
      _ ≤ _ := le_mul_of_one_le_right (by positivity) hσ
  have hb : b≤P := by linarith [log_nonneg (by norm_num : (1:ℝ)≤1000000)]
  have hab : b+log 4+2*log 2000≤1002*P := by
    have h4:=log_le_sub_one_of_pos (by norm_num : (0:ℝ)<4)
    have h2:=log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2000)
    linarith
  have hinner : (h:ℝ)*(potential ((Nat.card K:ℝ)^(d+3))
      ((univ,univ) : ChronoDomains (K:=K) (V:=V))+(w:ℝ)*(b+log 4+2*log 2000))+
      (w:ℝ)*P ≤ (2*((d:ℝ)+4)+1003)*(h:ℝ)*(σ+(w:ℝ)*P) := by
    calc
      _ ≤ (h:ℝ)*(2*((d:ℝ)+4)*σ+(w:ℝ)*(1002*P))+(w:ℝ)*P := by
        gcongr
      _ ≤ (h:ℝ)*(2*((d:ℝ)+4)*σ+(w:ℝ)*(1002*P))+(h:ℝ)*((w:ℝ)*P) := by
        exact add_le_add le_rfl (le_mul_of_one_le_left (mul_nonneg (Nat.cast_nonneg w) hP0) hh1)
      _ ≤ _ := by
        have h1 : 0≤(h:ℝ)*σ:=by positivity
        have h2 : 0≤(2*((d:ℝ)+4))*(h:ℝ)*((w:ℝ)*P):=by positivity
        nlinarith only [h1,h2]
  unfold reciprocalOutputCost
  simp only [Fintype.card_fin,Nat.cast_add,Nat.cast_one]
  have haux : (w:ℝ)*(log ((w:ℝ)+1)+headerCost (K:=K) (V:=V)+log ((m:ℝ)+1))≤
      (w:ℝ)*((2*C+2*((d:ℝ)+4))*σ) := by
    apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg w)
    linarith
  calc
    _ ≤ 3*(w:ℝ)*σ+(w:ℝ)*((2*C+2*((d:ℝ)+4))*σ)+
        (2*(H+22)*(Nat.card K:ℝ)*P)*((2*((d:ℝ)+4)+1003)*(h:ℝ)*(σ+(w:ℝ)*P)) := by
      exact add_le_add (add_le_add (by simpa only [Nat.cast_add,Nat.cast_one] using hshape) haux)
        (mul_le_mul_of_nonneg_left hinner (by positivity))
    _ = _ := by ring
end
end SharpLogRamsey.ActualPivot

end

end OAI
