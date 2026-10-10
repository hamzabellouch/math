import OAI.Analysis.Triangular.Envelope.KernelBounds
import OAI.Analysis.Triangular.Construction.L1Matrix
import OAI.Analysis.Triangular.Certificate.Inverse

namespace OAI

noncomputable section
open scoped BigOperators lp
namespace AtomicTriangular.Construction
open AtomicTriangular.L1Kernel AtomicTriangular.MatrixBounds
abbrev FiniteCoefficients := ℓ¹(Fin 20,ℝ)
abbrev TailCoefficients := ℓ¹(TailNode × Fin 2,ℝ)
lemma sum_fin20_pairs (g : Fin 10 → Fin 2 → ℝ) :
    (∑ i : Fin 20, g ⟨i.val/2,by omega⟩ ⟨i.val%2,by omega⟩) =
      ∑ n : Fin 10, ∑ d : Fin 2, g n d := by
  simpa only [finProdFinEquiv_symm_apply,Fintype.sum_prod_type,Fin.divNat,Fin.modNat] using
    ((finProdFinEquiv (m:=10) (n:=2)).symm.sum_comp (fun p => g p.1 p.2))
def Bkernel (i : Fin 20) (p : TailNode × Fin 2) : ℝ :=
  tailJet h H (finiteNode ⟨i.val/2,by omega⟩) p.1.val.val p.2 ⟨i.val%2,by omega⟩
lemma Bkernel_bound (p : TailNode × Fin 2) : (∑' i, |Bkernel i p|) ≤ 335 := by
  rw [tsum_fintype]
  change (∑ i : Fin 20, |tailJet h H (finiteNode ⟨i.val/2,by omega⟩) p.1.val.val p.2 ⟨i.val%2,by omega⟩|) ≤ 335
  exact (sum_fin20_pairs (fun n d => |tailJet h H (finiteNode n) p.1.val.val p.2 d|)).trans_le (finite_tail_column_bound _ _).le
def Boperator : TailCoefficients →L[ℝ] FiniteCoefficients :=
  operator Bkernel (fun _ => (hasSum_fintype _).summable) 335 Bkernel_bound
lemma Boperator_norm : ‖Boperator‖ ≤ 335 := operator_norm _ _ _ (by norm_num) _
def Ckernel (p : TailNode × Fin 2) (i : Fin 20) : ℝ :=
  jet H h p.1.val.val p.2 (finiteColumn ⟨i.val+2,by omega⟩)
lemma Ckernel_summable (i : Fin 20) : Summable (fun p => |Ckernel p i|) :=
  (tail_atom_column_bounds 1 0 _).1
lemma Ckernel_bound (i : Fin 20) : (∑' p, |Ckernel p i|) ≤ 7/10^15 :=
  (tail_finite_column_bound ⟨i.val+2,by omega⟩).le
def Coperator : FiniteCoefficients →L[ℝ] TailCoefficients :=
  operator Ckernel Ckernel_summable (7/10^15) Ckernel_bound
lemma Coperator_norm : ‖Coperator‖ ≤ 7/10^15 := operator_norm _ _ _ (by norm_num) _
def Dkernel (p q : TailNode × Fin 2) : ℝ :=
  tailJet h h p.1.val.val q.1.val.val q.2 p.2
lemma Dkernel_summable (q : TailNode × Fin 2) : Summable (fun p => |Dkernel p q|) :=
  (tail_tail_column_bounds 0 0 q.1.val.val q.2).1
lemma Dkernel_bound (q : TailNode × Fin 2) : (∑' p, |Dkernel p q|) ≤ 23/10^9 :=
  (tail_tail_column_bound q.1.val.val q.2).le
def Doperator : TailCoefficients →L[ℝ] TailCoefficients :=
  operator Dkernel Dkernel_summable (23/10^9) Dkernel_bound
lemma Doperator_norm : ‖Doperator‖ ≤ 23/10^9 := operator_norm _ _ _ (by norm_num) _
def tailFixedColumn (c : Fin 23) : TailCoefficients :=
  column (fun p (_ : Unit) => jet (if c.val=22 then h else H) h p.1.val.val p.2 (finiteColumn c))
    (fun _ => by
      by_cases hc : c.val=22
      · have hh := (tail_atom_column_bounds 0 0 (finiteColumn c)).1
        simpa [hc,damping] using hh
      · have hh := (tail_atom_column_bounds 1 0 (finiteColumn c)).1
        simpa [hc,damping] using hh) ()
lemma tailFixedColumn_apply (c : Fin 23) (p : TailNode × Fin 2) :
    tailFixedColumn c p = jet (if c.val=22 then h else H) h p.1.val.val p.2 (finiteColumn c) := rfl
lemma tailFixedColumn_norm_finite (c : Fin 22) : ‖tailFixedColumn ⟨c.val,by omega⟩‖ ≤ 7/10^15 := by
  rw [l1_norm]
  have hc : c.val≠22 := by omega
  simp only [tailFixedColumn_apply,hc,↓reduceIte]
  exact (tail_finite_column_bound c).le
lemma tailFixedColumn_norm_constant : ‖tailFixedColumn 22‖ ≤ 127/10^9 := by
  rw [l1_norm]
  simp only [tailFixedColumn_apply,Fin.isValue]
  have hh := tail_constant_column_bound
  convert hh.le using 1
  rfl

def Roperator : FiniteCoefficients →L[ℝ] FiniteCoefficients := l1Matrix R
def Lplus : FiniteCoefficients →L[ℝ] FiniteCoefficients := l1Matrix (1-R)⁻¹
def Lminus : FiniteCoefficients →L[ℝ] FiniteCoefficients := l1Matrix (1+R)⁻¹
lemma Lplus_norm : ‖Lplus‖ ≤ 17 :=
  ((l1Matrix_norm _).trans_lt FiniteCertificate.minusInverse_bound).le.trans (by norm_num)
lemma Lminus_norm : ‖Lminus‖ ≤ 5 :=
  ((l1Matrix_norm _).trans_lt FiniteCertificate.plusInverse_bound).le.trans (by norm_num)
lemma Lplus_left_inverse : (1-Roperator).comp Lplus=1 := by
  have hh := (l1Matrix_inverse (1-R) FiniteCertificate.minusBlock_isUnit).1
  simpa [Lplus,l1Matrix_sub,l1Matrix_one,Roperator] using hh
lemma Lminus_left_inverse : (1+Roperator).comp Lminus=1 := by
  have hh := (l1Matrix_inverse (1+R) FiniteCertificate.plusBlock_isUnit).1
  simpa [Lminus,l1Matrix_add,l1Matrix_one,Roperator] using hh
end AtomicTriangular.Construction
end

end OAI
