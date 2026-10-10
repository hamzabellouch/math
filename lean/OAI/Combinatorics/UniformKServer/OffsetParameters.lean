import Mathlib
import OAI.Combinatorics.UniformKServer.ComputedInstance
import OAI.Combinatorics.UniformKServer.OffsetTable

namespace OAI

noncomputable section
                                       
section

/-! Terminating rational search for the restart length. The uniform finite-law
endpoint is used only to prove termination, never supplied to the constructor. -/
namespace UniformKServer.OffsetParameters
open EffectiveLP ComputedInstance
variable {n k : ℕ} [NeZero k]

def cap (hn : 2 ≤ n) (d : RationalMetric n) (R : ℕ) : ℕ :=
  ⌈(R:ℚ)*(k+1)*diameter hn d / separation hn d⌉₊

def acceptable (hn : 2 ≤ n) (d : RationalMetric n) (u : Config n k) (A : ℚ) (R : ℕ) : Prop :=
  0 < R ∧ (k:ℚ)*diameter hn d ≤ (R:ℚ)*separation hn d ∧
    OffsetTable.offset d u A (horizon k (cap (k:=k) hn d R)) ≤ (R:ℚ)*separation hn d

instance acceptableDecidable (hn : 2 ≤ n) (d : RationalMetric n) (u : Config n k)
    (A : ℚ) (R : ℕ) : Decidable (acceptable hn d u A R) := inferInstanceAs (Decidable (_ ∧ _ ∧ _))

theorem search_exists (hn : 2 ≤ n) (hk : 2 ≤ k) (d : RationalMetric n)
    (u : Config n k) (A : ℚ)
    (hA : PartitionTree.absoluteRate*(Real.log (k+1))^2 ≤ (A : ℝ)) :
    ∃R : ℕ,acceptable hn d u A R := by
  obtain ⟨B,hB,hbound⟩ := OffsetTable.computed_uniform d u hk A hA
  obtain ⟨hD,hδ,hdiam,hsep,-⟩ := ComputedInstance.parameters hn (NeZero.pos k) d
  let W : ℝ := max ((k:ℝ)*(diameter hn d : ℝ)) B
  obtain ⟨R,hR⟩ := exists_nat_gt (W/(separation hn d : ℝ))
  have hW : 0 ≤ W := (by positivity : 0 ≤ ((k:ℝ)*(diameter hn d : ℝ))).trans (le_max_left _ _)
  have hpos : 0 < R := by
    have hg : (0:ℝ) < R := (div_nonneg hW hδ.le).trans_lt hR
    exact_mod_cast hg
  have hmul : W ≤ (R:ℝ)*(separation hn d : ℝ) :=
    ((div_lt_iff₀ hδ).mp hR).le
  refine ⟨R,hpos,?_,?_⟩
  · exact_mod_cast (le_max_left ((k:ℝ)*(diameter hn d : ℝ)) B).trans hmul
  · have he := (hbound (horizon k (cap (k:=k) hn d R))).2
    exact_mod_cast he.trans ((le_max_right _ _).trans hmul)

def restart (hn : 2 ≤ n) (hk : 2 ≤ k) (d : RationalMetric n)
    (u : Config n k) (A : ℚ)
    (hA : PartitionTree.absoluteRate*(Real.log (k+1))^2 ≤ (A : ℝ)) : ℕ :=
  Nat.find (search_exists hn hk d u A hA)

theorem restart_spec (hn : 2 ≤ n) (hk : 2 ≤ k) (d : RationalMetric n)
    (u : Config n k) (A : ℚ)
    (hA : PartitionTree.absoluteRate*(Real.log (k+1))^2 ≤ (A : ℝ)) :
    acceptable hn d u A (restart hn hk d u A hA) := Nat.find_spec _

theorem cap_bound (hn : 2 ≤ n) (d : RationalMetric n) (R : ℕ) :
    (R:ℝ)*(k+1)*(diameter hn d : ℝ) ≤
      ((cap (k:=k) hn d R : ℝ)+1)*(separation hn d : ℝ) := by
  have hs : 0 < separation hn d := by
    exact_mod_cast (ComputedInstance.parameters hn (NeZero.pos k) d).2.1
  have hb : (R:ℚ)*(k+1)*diameter hn d ≤
      (cap (k:=k) hn d R : ℚ)*separation hn d := (div_le_iff₀ hs).mp (Nat.le_ceil _)
  have hb' : (R:ℚ)*(k+1)*diameter hn d ≤
      ((cap (k:=k) hn d R : ℚ)+1)*separation hn d := by nlinarith
  exact_mod_cast hb'

theorem overhead_bound (hn : 2 ≤ n) (hk : 2 ≤ k) (d : RationalMetric n)
    (u : Config n k) (A : ℚ) (hA : 0 ≤ A) (R : ℕ) (hR : acceptable hn d u A R) :
    (2*(A : ℝ)+1)*k*(diameter hn d : ℝ)+
      2*(OffsetTable.offset d u A (horizon k (cap (k:=k) hn d R)) : ℝ)+2*(diameter hn d : ℝ) ≤
      (2*(A : ℝ)+4)*R*(separation hn d : ℝ) := by
  have ha : 0 ≤ (A : ℝ) := by exact_mod_cast hA
  have hD := (ComputedInstance.parameters hn (NeZero.pos k) d).1
  have hkd : (k:ℝ)*(diameter hn d : ℝ) ≤ (R:ℝ)*(separation hn d : ℝ) := by exact_mod_cast hR.2.1
  have he : (OffsetTable.offset d u A (horizon k (cap (k:=k) hn d R)) : ℝ) ≤
      (R:ℝ)*(separation hn d : ℝ) := by exact_mod_cast hR.2.2
  have hk' : (2:ℝ) ≤ k := by exact_mod_cast hk
  have hx := mul_le_mul_of_nonneg_left hkd (show 0 ≤ 2*(A : ℝ)+1 by positivity)
  have hy := mul_le_mul_of_nonneg_right hk' hD
  nlinarith only [hx,hy,hkd,he]

end UniformKServer.OffsetParameters

end


end

end OAI
