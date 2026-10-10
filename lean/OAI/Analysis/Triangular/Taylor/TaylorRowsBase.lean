import OAI.Analysis.Triangular.Certificate.PolytopeInterval
import OAI.Analysis.Triangular.Taylor.TaylorSpectrum
import OAI.Analysis.Triangular.Taylor.TaylorWave00
import OAI.Analysis.Triangular.Taylor.TaylorWave01
import OAI.Analysis.Triangular.Taylor.TaylorWave10
import OAI.Analysis.Triangular.Taylor.TaylorWave11

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.Construction

def nearDisplacementNum : Fin 7 → Fin 2 → ℤ :=
  ![![-2,2],![-2,1],![-1,3],![-3,2],![-2,3],![-3,1],![-1,3]]
def nearDisplacement (n : Fin 7) (y : Fin 2) : ℝ := nearDisplacementNum n y / 2
end AtomicTriangular.Construction
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval

def taylorWaveTable : Fin 2 → Fin 2 → Fin 7 → Fin 21 → Fin 31 → CI :=
  ![![tw0_0,tw0_1],![tw1_0,tw1_1]]
lemma taylorWaveTable_mem (q br : Fin 2) (n : Fin 7) (l : Fin 21) (j : Fin 31) :
    (taylorWaveTable q br n l j).Mem (taylorWave q br (nearNode n) l.val (frequency j)) := by
  fin_cases q <;> fin_cases br
  · exact tw0_0_mem n l j
  · exact tw0_1_mem n l j
  · exact tw1_0_mem n l j
  · exact tw1_1_mem n l j

def nearDisplacementBox (n : Fin 7) (y : Fin 2) : RI := (RI.point (nearDisplacementNum n y)).divNat 2
lemma nearDisplacementBox_mem (n : Fin 7) (y : Fin 2) :
    (nearDisplacementBox n y).Mem (nearDisplacement n y) := by
  exact RI.mem_divNat (RI.mem_point _) (by norm_num)
def taylorRowBox (side : Fin 2) (n : Fin 7) (y : Fin 2) (l : Fin 21) (r : Fin 8) : RI :=
  ((nearDisplacementBox n y).pow l.val).mul
    (CI.sum (fun q : Fin 2 => CI.sum (fun j : Fin 31 =>
      ((spectrumTable side q j r).mul (taylorWaveTable q 0 n l j)).add
      ((spectrumTable (otherSide side) q j r).mul (taylorWaveTable q 1 n l j))))).re
lemma taylorRowBox_mem (side : Fin 2) (n : Fin 7) (y : Fin 2) (l : Fin 21) (r : Fin 8) :
    (taylorRowBox side n y l r).Mem
      (taylorRow side (nearNode n) (nearDisplacement n y) l.val r) := by
  exact RI.mem_mul (RI.mem_pow (nearDisplacementBox_mem n y) l.val)
    (CI.mem_sum (fun q => CI.mem_sum (fun j => CI.mem_add
      (CI.mem_mul (spectrumTable_mem side q j r) (taylorWaveTable_mem q 0 n l j))
      (CI.mem_mul (spectrumTable_mem (otherSide side) q j r) (taylorWaveTable_mem q 1 n l j))))).1

def bernsteinRowsBox (n : ℕ) (a : Fin (n+1) → Fin 8 → RI)
    (d : Fin (n+1)) (r : Fin 8) : RI :=
  RI.sum (fun l : Fin (n+1) => ((RI.point (d.val.choose l.val)).divNat (n.choose l.val)).mul (a l r))
lemma bernsteinRowsBox_mem (n : ℕ) {a : Fin (n+1) → Fin 8 → RI}
    {v : Fin (n+1) → Fin 8 → ℝ} (hv : ∀ l r, (a l r).Mem (v l r))
    (d : Fin (n+1)) (r : Fin 8) :
    (bernsteinRowsBox n a d r).Mem (bernsteinRows n v d r) := by
  apply RI.mem_sum
  intro l
  apply RI.mem_mul _ (hv l r)
  have hh := RI.mem_divNat (RI.mem_point (d.val.choose l.val))
    (Nat.choose_pos (show l.val≤n by omega))
  simpa only [Int.cast_natCast] using hh
end AtomicTriangular.FiniteCertificate
end

end OAI
