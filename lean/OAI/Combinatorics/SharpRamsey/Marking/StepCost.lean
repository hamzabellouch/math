import Mathlib
import OAI.Combinatorics.SharpRamsey.Windows.WindowChoices
import OAI.Combinatorics.SharpRamsey.Windows.LogWindow

namespace OAI

section
namespace SharpLogRamsey.ActualPivot
open Real Filter SourceScales
open scoped Classical Topology
noncomputable section

theorem eventually_reciprocal_message_cost (i : ℕ) (η c C H : ℝ)
    (hη : 0 < η) (hc : 0 < c) (hC : 0 < C) (hH : 0 ≤ H) :
    ∀ᶠ σ : ℝ in atTop, ∀ (q : ℕ) [Fact q.Prime], exp σ=(q:ℝ) →
    ∀ (V : Type) [AddCommGroup V] [Module (ZMod q) V] [FiniteDimensional (ZMod q) V]
      [Fintype (Projectivization (ZMod q) V)]
      [Fintype (Projectivization (ZMod q) (Module.Dual (ZMod q) V))]
      [Fintype (Projectivization (ZMod q) (Module.Dual (ZMod q) (Module.Dual (ZMod q) V)))],
      Module.finrank (ZMod q) V=i+4 →
    ∀ (D : ℝ) (R w n k m : ℕ), Admissible σ η D R →
      1 ≤ w → c*(q:ℝ)*σ^(1+η) ≤ m →
      (w:ℝ)*D ≤ C*σ^(1+η/2) → (w:ℝ) ≤ C*σ^(1+η/2) →
      (4*(n+k):ℕ) ≤ C*(q:ℝ)*σ^(1+η/2) →
      4 ≤ scaleP σ η D R → 16*scaleKstar σ η D+log 1000000 ≤ scaleP σ η D R →
    reciprocalOutputCost (K:=ZMod q) (V:=V) (I:=Fin w)
      (d:=i+1) (b:=16*scaleKstar σ η D) (P:=scaleP σ η D R) (H:=H)
      w (Nat.log 2 w+1) (2*(n+k)) ≤ D*σ^(-η/3)*m := by
  let a:=1+η/2
  let Cl:=a+2
  let A:=2*(H+22)*(2*(((i+1:ℕ):ℝ)+4)+1003)
  let B:=3+2*Cl+2*(((i+1:ℕ):ℝ)+4)
  have ha : 0 ≤ a:=by dsimp only [a];linarith
  have hA : 0 ≤ A:=by dsimp only [A];positivity
  have hB : 0 ≤ B:=by dsimp only [B,Cl,a];positivity
  filter_upwards [eventually_literal_cost_contraction η A B C c hη hA hB hC.le hc,
    ChronologicalTree.eventually_natLog_small (beta η) C a (beta_pos hη) hC,
    eventually_log_window C a hC ha,eventually_ge_atTop (1:ℝ)]
      with σ hcost hheight hlogwin hσ
  intro q _ he V _ _ _ _ _ _ hdim D R w n k m had hw hmlo hwD hwup hLup hP hbP
  have hσ0 : 0 < σ:=by linarith
  have hD : 1 ≤ D:=(one_le_rpow hσ (beta_pos hη).le).trans had.D_lower
  have hqlog : log (Nat.card (ZMod q):ℝ)=σ:=by rw [Nat.card_zmod,←he,log_exp]
  have hwlog : log ((w:ℝ)+1) ≤ Cl*σ:=by
    apply hlogwin _ (Nat.cast_nonneg _)
    have he1 : 1 ≤ exp σ:=one_le_exp hσ0.le
    calc
      _ ≤ C*σ^a:=hwup
      _ ≤ C*exp σ*σ^a:=by nlinarith [mul_le_mul_of_nonneg_right he1 (by positivity : 0 ≤ C*σ^a)]
  have hmlog : log ((2*(n+k):ℕ)+1:ℝ) ≤ Cl*σ:=by
    apply hlogwin _ (Nat.cast_nonneg _)
    calc
      _ ≤ ((4*(n+k):ℕ):ℝ):=by push_cast;linarith [show (0:ℝ) ≤ n by positivity,show (0:ℝ) ≤ k by positivity]
      _ ≤ C*(q:ℝ)*σ^a:=hLup
      _ = C*exp σ*σ^a:=by rw [he]
  apply (reciprocal_cost_envelope hdim hqlog hσ hw
    (show 1 ≤ Nat.log 2 w+1 by omega) hH hP hbP hwlog hmlog (m:=2*(n+k))).trans
  simpa only [A,B,Nat.card_zmod,Nat.cast_add,Nat.cast_one] using
    hcost (q:ℝ) D (scaleP σ η D R) (Nat.log 2 w+1:ℝ) (w:ℝ) (m:ℝ)
      he hD (by linarith) (P_upper_D hσ hη had) (by positivity)
      (by simpa only [Nat.cast_add,Nat.cast_one] using hheight w hwup)
      (Nat.cast_nonneg _) hwD hmlo
end
end SharpLogRamsey.ActualPivot

end

end OAI
