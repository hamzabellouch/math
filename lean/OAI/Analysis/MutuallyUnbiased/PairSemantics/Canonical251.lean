import OAI.Analysis.MutuallyUnbiased.PairSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes0
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes2
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes4
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes12
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes15
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes16
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes18
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes19
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes20
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes37
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes40
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes41
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes42
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes43

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw8032 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -2, -1, 3], ![-1, 1, -1, 1], ![0, 1, 3, -4], ![1, 0, -1, 0]]

def raw8032step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -1, 0, 1], ![-2, 1, 1, 0], ![-1, -1, 3, -1], ![3, 1, -4, 0]]

def raw8032step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, 1, -2, 1], ![0, 1, 3, -4], ![1, -1, 0, 0]]

theorem canonical8032 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8032 = injectiveMoment H node985 := by
  calc
    injectiveMoment H raw8032 = injectiveMoment H raw8032step0 := by
      have heq : raw8032step0 = raw8032.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw8032).symm
    injectiveMoment H raw8032step0 = injectiveMoment H raw8032step1 := by
      have heq : raw8032step1 = (fun i j => raw8032step0 (permutation24 i) (permutation29 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8032step0 permutation24 permutation29
    _ = injectiveMoment H node985 := by rfl

def raw8033 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -2, -1, 3], ![-1, 1, 1, -1], ![0, 1, 1, -2], ![1, 0, -1, 0]]

def raw8033step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 2, 1, -3], ![1, -1, -1, 1], ![0, -1, -1, 2], ![-1, 0, 1, 0]]

def raw8033step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 1, 0], ![0, -1, -1, 2], ![0, 2, 1, -3], ![1, -1, -1, 1]]

theorem canonical8033 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw8033 = injectiveMoment H node1299 := by
  calc
    injectiveMoment H raw8033 = injectiveMoment H raw8033step0 := by
      have heq : raw8033step0 = -raw8033 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw8033).symm
    injectiveMoment H raw8033step0 = injectiveMoment H raw8033step1 := by
      have heq : raw8033step1 = (fun i j => raw8033step0 (permutation31 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8033step0 permutation31 permutation9
    _ = injectiveMoment H node1299 := by rfl

def raw8034 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, -2, -1, 3], ![-1, 2, 3, -4], ![1, 0, -2, 1]]

def raw8034step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -1, 1], ![-2, 2, 0], ![-1, 3, -2], ![3, -4, 1]]

def raw8034step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -2, 2], ![1, 0, -1], ![1, 3, -4]]

theorem canonical8034 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8034 = injectiveMoment H node166 := by
  calc
    injectiveMoment H raw8034 = injectiveMoment H raw8034step0 := by
      have heq : raw8034step0 = raw8034.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw8034).symm
    injectiveMoment H raw8034step0 = injectiveMoment H raw8034step1 := by
      have heq : raw8034step1 = (fun i j => raw8034step0 (permutation23 i) (permutation7 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8034step0 permutation23 permutation7
    _ = injectiveMoment H node166 := by rfl

def raw8035 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -2, -1, 3], ![0, 0, 1, -1], ![-1, 0, 1, 0], ![0, 2, -1, -1], ![1, 0, 0, -1]]

def raw8035step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 2, 1, -3], ![0, 0, -1, 1], ![1, 0, -1, 0], ![0, -2, 1, 1], ![-1, 0, 0, 1]]

def raw8035step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -2, 1, 1], ![0, 0, -1, 1], ![0, 2, 1, -3], ![1, 0, -1, 0]]

theorem canonical8035 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw8035 = injectiveMoment H node2742 := by
  calc
    injectiveMoment H raw8035 = injectiveMoment H raw8035step0 := by
      have heq : raw8035step0 = -raw8035 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw8035).symm
    injectiveMoment H raw8035step0 = injectiveMoment H raw8035step1 := by
      have heq : raw8035step1 = (fun i j => raw8035step0 (permutation147 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8035step0 permutation147 permutation9
    _ = injectiveMoment H node2742 := by rfl

def raw8036 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -2, -1, 3], ![0, 0, 1, -1], ![-1, 1, 1, -1], ![0, 1, 0, -1], ![1, 0, -1, 0]]

def raw8036step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 2, 1, -3], ![0, 0, -1, 1], ![1, -1, -1, 1], ![0, -1, 0, 1], ![-1, 0, 1, 0]]

def raw8036step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 1, 0], ![0, -1, 0, 1], ![0, 0, -1, 1], ![0, 2, 1, -3], ![1, -1, -1, 1]]

theorem canonical8036 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw8036 = injectiveMoment H node2813 := by
  calc
    injectiveMoment H raw8036 = injectiveMoment H raw8036step0 := by
      have heq : raw8036step0 = -raw8036 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw8036).symm
    injectiveMoment H raw8036step0 = injectiveMoment H raw8036step1 := by
      have heq : raw8036step1 = (fun i j => raw8036step0 (permutation147 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8036step0 permutation147 permutation9
    _ = injectiveMoment H node2813 := by rfl

def raw8037 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -2, -1, 3], ![0, 0, 1, -1], ![-1, 2, 1, -2], ![1, 0, -1, 0]]

def raw8037step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-2, 0, 2, 0], ![-1, 1, 1, -1], ![3, -1, -2, 0]]

def raw8037step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![0, 0, 2, -2], ![0, 1, -1, 0], ![1, -1, 1, -1]]

theorem canonical8037 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8037 = injectiveMoment H node1220 := by
  calc
    injectiveMoment H raw8037 = injectiveMoment H raw8037step0 := by
      have heq : raw8037step0 = raw8037.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw8037).symm
    injectiveMoment H raw8037step0 = injectiveMoment H raw8037step1 := by
      have heq : raw8037step1 = (fun i j => raw8037step0 (permutation29 i) (permutation20 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8037step0 permutation29 permutation20
    _ = injectiveMoment H node1220 := by rfl

def raw8038 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -2, -1, 3], ![0, 0, 1, -1], ![0, 0, 1, -1], ![-1, 2, -1, 0], ![1, 0, 0, -1]]

def raw8038step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 2, 0], ![0, -1, -2, 3], ![0, 1, 0, -1], ![0, 1, 0, -1], ![1, 0, 0, -1]]

theorem canonical8038 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8038 = injectiveMoment H node2676 := by
  calc
    injectiveMoment H raw8038 = injectiveMoment H raw8038step0 := by
      have heq : raw8038step0 = (fun i j => raw8038 (permutation104 i) (permutation11 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8038 permutation104 permutation11
    _ = injectiveMoment H node2676 := by rfl

def raw8039 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -2, -1, 3], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 2, -1, -1], ![0, 0, 0, 0]]

def raw8039step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -2, -1, 3], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 2, -1, -1]]

def raw8039step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 1, -1], ![2, -1, -1]]

theorem canonical8039 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8039 = injectiveMoment H node176 := by
  calc
    injectiveMoment H raw8039 = injectiveMoment H raw8039step0 := by
      have hz : ∀ j, raw8039 (permutation128 0) j = 0 := by decide +kernel
      have heq : raw8039step0 = (fun i j => raw8039 (permutation128 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw8039 permutation128 hz
    injectiveMoment H raw8039step0 = injectiveMoment H raw8039step1 := by
      have hz : ∀ i, raw8039step0 i (permutation9 0) = 0 := by decide +kernel
      have heq : raw8039step1 = (fun i j => raw8039step0 i (permutation9 j.succ)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_column (by decide) H raw8039step0 permutation9 hz
    _ = injectiveMoment H node176 := by rfl

def raw8040 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -2, -1, 3], ![0, 0, 1, -1], ![0, 1, 0, -1], ![-1, 1, 1, -1], ![1, 0, -1, 0]]

def raw8040step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 2, 1, -3], ![0, 0, -1, 1], ![0, -1, 0, 1], ![1, -1, -1, 1], ![-1, 0, 1, 0]]

def raw8040step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 1, 0], ![0, -1, 0, 1], ![0, 0, -1, 1], ![0, 2, 1, -3], ![1, -1, -1, 1]]

theorem canonical8040 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw8040 = injectiveMoment H node2813 := by
  calc
    injectiveMoment H raw8040 = injectiveMoment H raw8040step0 := by
      have heq : raw8040step0 = -raw8040 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw8040).symm
    injectiveMoment H raw8040step0 = injectiveMoment H raw8040step1 := by
      have heq : raw8040step1 = (fun i j => raw8040step0 (permutation141 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8040step0 permutation141 permutation9
    _ = injectiveMoment H node2813 := by rfl

def raw8041 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -2, -1, 3], ![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![0, 0, 0, 0]]

def raw8041step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -2, -1, 3], ![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 1, 0, -1]]

def raw8041step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1]]

def raw8041step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -2, 3], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1]]

theorem canonical8041 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8041 = injectiveMoment H node271 := by
  calc
    injectiveMoment H raw8041 = injectiveMoment H raw8041step0 := by
      have hz : ∀ j, raw8041 (permutation128 0) j = 0 := by decide +kernel
      have heq : raw8041step0 = (fun i j => raw8041 (permutation128 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw8041 permutation128 hz
    injectiveMoment H raw8041step0 = injectiveMoment H raw8041step1 := by
      have hz : ∀ i, raw8041step0 i (permutation9 0) = 0 := by decide +kernel
      have heq : raw8041step1 = (fun i j => raw8041step0 i (permutation9 j.succ)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_column (by decide) H raw8041step0 permutation9 hz
    injectiveMoment H raw8041step1 = injectiveMoment H raw8041step2 := by
      have heq : raw8041step2 = (fun i j => raw8041step1 (permutation12 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8041step1 permutation12 permutation5
    _ = injectiveMoment H node271 := by rfl

def raw8042 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -2, -1, 3], ![0, 0, 1, -1], ![0, 2, 1, -3], ![0, 0, -1, 1]]

def raw8042step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![2, 1, -3], ![0, -1, 1]]

def raw8042step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, 1, -1], ![2, 1, -3]]

theorem canonical8042 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8042 = injectiveMoment H node168 := by
  calc
    injectiveMoment H raw8042 = injectiveMoment H raw8042step0 := by
      have hz : ∀ i, raw8042 i (permutation9 0) = 0 := by decide +kernel
      have heq : raw8042step0 = (fun i j => raw8042 i (permutation9 j.succ)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_column (by decide) H raw8042 permutation9 hz
    injectiveMoment H raw8042step0 = injectiveMoment H raw8042step1 := by
      have heq : raw8042step1 = (fun i j => raw8042step0 (permutation13 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8042step0 permutation13 permutation3
    _ = injectiveMoment H node168 := by rfl

def raw8043 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -2, -1, 3], ![0, 0, 2, -2], ![-1, 1, -1, 1], ![0, 1, 0, -1], ![1, 0, 0, -1]]

def raw8043step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, -1, -2, 3], ![0, 0, 1, -1], ![0, 2, 0, -2], ![1, 0, 0, -1]]

theorem canonical8043 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8043 = injectiveMoment H node2619 := by
  calc
    injectiveMoment H raw8043 = injectiveMoment H raw8043step0 := by
      have heq : raw8043step0 = (fun i j => raw8043 (permutation82 i) (permutation11 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8043 permutation82 permutation11
    _ = injectiveMoment H node2619 := by rfl

def raw8044 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -2, -1, 3], ![0, 0, 2, -2], ![0, 1, -1, 0], ![-1, 1, 0, 0], ![1, 0, 0, -1]]

def raw8044step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, 2, 1, -3], ![0, 0, -2, 2], ![0, -1, 1, 0], ![1, -1, 0, 0], ![-1, 0, 0, 1]]

def raw8044step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -2, 0, 2], ![0, 1, -1, 0], ![0, 1, 2, -3], ![1, 0, -1, 0]]

theorem canonical8044 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw8044 = injectiveMoment H node2740 := by
  calc
    injectiveMoment H raw8044 = injectiveMoment H raw8044step0 := by
      have heq : raw8044step0 = -raw8044 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw8044).symm
    injectiveMoment H raw8044step0 = injectiveMoment H raw8044step1 := by
      have heq : raw8044step1 = (fun i j => raw8044step0 (permutation135 i) (permutation11 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8044step0 permutation135 permutation11
    _ = injectiveMoment H node2740 := by rfl

def raw8045 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -2, -1, 3], ![0, 0, 2, -2], ![0, 1, -1, 0], ![0, 1, 0, -1], ![0, 0, 0, 0]]

def raw8045step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -2, -1, 3], ![0, 0, 2, -2], ![0, 1, -1, 0], ![0, 1, 0, -1]]

def raw8045step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1]]

theorem canonical8045 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8045 = injectiveMoment H node185 := by
  calc
    injectiveMoment H raw8045 = injectiveMoment H raw8045step0 := by
      have hz : ∀ j, raw8045 (permutation128 0) j = 0 := by decide +kernel
      have heq : raw8045step0 = (fun i j => raw8045 (permutation128 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw8045 permutation128 hz
    injectiveMoment H raw8045step0 = injectiveMoment H raw8045step1 := by
      have hz : ∀ i, raw8045step0 i (permutation9 0) = 0 := by decide +kernel
      have heq : raw8045step1 = (fun i j => raw8045step0 i (permutation9 j.succ)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_column (by decide) H raw8045step0 permutation9 hz
    _ = injectiveMoment H node185 := by rfl

def raw8046 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, -2, -1, 3], ![0, 0, 2, -2], ![0, 2, -1, -1]]

def raw8046step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 2, -2], ![2, -1, -1]]

theorem canonical8046 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8046 = injectiveMoment H node36 := by
  calc
    injectiveMoment H raw8046 = injectiveMoment H raw8046step0 := by
      have hz : ∀ i, raw8046 i (permutation9 0) = 0 := by decide +kernel
      have heq : raw8046step0 = (fun i j => raw8046 i (permutation9 j.succ)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_column (by decide) H raw8046 permutation9 hz
    _ = injectiveMoment H node36 := by rfl

def raw8047 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, -2, -1, 3], ![0, 0, 3, -3], ![0, 2, -2, 0]]

def raw8047step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 3, -3], ![2, -2, 0]]

theorem canonical8047 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8047 = injectiveMoment H node37 := by
  calc
    injectiveMoment H raw8047 = injectiveMoment H raw8047step0 := by
      have hz : ∀ i, raw8047 i (permutation9 0) = 0 := by decide +kernel
      have heq : raw8047step0 = (fun i j => raw8047 i (permutation9 j.succ)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_column (by decide) H raw8047 permutation9 hz
    _ = injectiveMoment H node37 := by rfl

def raw8048 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, -2, -1, 3], ![0, 1, -2, 1], ![0, 1, 3, -4]]

def raw8048step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, -1, 3], ![1, -2, 1], ![1, 3, -4]]

theorem canonical8048 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8048 = injectiveMoment H node40 := by
  calc
    injectiveMoment H raw8048 = injectiveMoment H raw8048step0 := by
      have hz : ∀ i, raw8048 i (permutation9 0) = 0 := by decide +kernel
      have heq : raw8048step0 = (fun i j => raw8048 i (permutation9 j.succ)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_column (by decide) H raw8048 permutation9 hz
    _ = injectiveMoment H node40 := by rfl

def raw8049 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -2, -1, 3], ![0, 1, -1, 0], ![-1, 1, 2, -2], ![1, 0, 0, -1]]

def raw8049step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-2, 1, 1, 0], ![-1, -1, 2, 0], ![3, 0, -2, -1]]

def raw8049step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![0, -1, 2, -1], ![0, 1, 1, -2], ![1, 0, -1, 0]]

theorem canonical8049 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8049 = injectiveMoment H node1207 := by
  calc
    injectiveMoment H raw8049 = injectiveMoment H raw8049step0 := by
      have heq : raw8049step0 = raw8049.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw8049).symm
    injectiveMoment H raw8049step0 = injectiveMoment H raw8049step1 := by
      have heq : raw8049step1 = (fun i j => raw8049step0 (permutation32 i) (permutation30 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8049step0 permutation32 permutation30
    _ = injectiveMoment H node1207 := by rfl

def raw8050 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -2, -1, 3], ![0, 1, -1, 0], ![0, 1, 2, -3], ![0, 0, 0, 0]]

def raw8050step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 0, 0, 0], ![-2, 1, 1, 0], ![-1, -1, 2, 0], ![3, 0, -3, 0]]

def raw8050step1 : Matrix (Fin 3) (Fin 4) ℤ := ![![-2, 1, 1, 0], ![-1, -1, 2, 0], ![3, 0, -3, 0]]

def raw8050step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![3, 0, -3]]

def raw8050step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-1, -1, 2], ![0, 3, -3], ![1, -2, 1]]

theorem canonical8050 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8050 = injectiveMoment H node63 := by
  calc
    injectiveMoment H raw8050 = injectiveMoment H raw8050step0 := by
      have heq : raw8050step0 = raw8050.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw8050).symm
    injectiveMoment H raw8050step0 = injectiveMoment H raw8050step1 := by
      have hz : ∀ j, raw8050step0 (permutation9 0) j = 0 := by decide +kernel
      have heq : raw8050step1 = (fun i j => raw8050step0 (permutation9 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw8050step0 permutation9 hz
    injectiveMoment H raw8050step1 = injectiveMoment H raw8050step2 := by
      have hz : ∀ i, raw8050step1 i (permutation27 0) = 0 := by decide +kernel
      have heq : raw8050step2 = (fun i j => raw8050step1 i (permutation27 j.succ)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_column (by decide) H raw8050step1 permutation27 hz
    injectiveMoment H raw8050step2 = injectiveMoment H raw8050step3 := by
      have heq : raw8050step3 = (fun i j => raw8050step2 (permutation6 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8050step2 permutation6 permutation5
    _ = injectiveMoment H node63 := by rfl

def raw8051 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -2, -1, 3], ![0, 1, 0, -1], ![-1, 1, 2, -2], ![1, 0, -1, 0]]

def raw8051step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 0, -1, 1], ![-2, 1, 1, 0], ![-1, 0, 2, -1], ![3, -1, -2, 0]]

def raw8051step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![0, -1, 2, -1], ![0, 1, -1, 0], ![1, 0, 1, -2]]

theorem canonical8051 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8051 = injectiveMoment H node1206 := by
  calc
    injectiveMoment H raw8051 = injectiveMoment H raw8051step0 := by
      have heq : raw8051step0 = raw8051.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw8051).symm
    injectiveMoment H raw8051step0 = injectiveMoment H raw8051step1 := by
      have heq : raw8051step1 = (fun i j => raw8051step0 (permutation31 i) (permutation20 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8051step0 permutation31 permutation20
    _ = injectiveMoment H node1206 := by rfl

def raw8052 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -2, -1, 3], ![0, 1, 0, -1], ![0, 1, 1, -2], ![0, 0, 0, 0]]

def raw8052step0 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, -2, -1, 3], ![0, 1, 0, -1], ![0, 1, 1, -2]]

def raw8052step1 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, -1, 3], ![1, 0, -1], ![1, 1, -2]]

def raw8052step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-1, -2, 3], ![0, 1, -1], ![1, 1, -2]]

theorem canonical8052 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8052 = injectiveMoment H node56 := by
  calc
    injectiveMoment H raw8052 = injectiveMoment H raw8052step0 := by
      have hz : ∀ j, raw8052 (permutation27 0) j = 0 := by decide +kernel
      have heq : raw8052step0 = (fun i j => raw8052 (permutation27 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw8052 permutation27 hz
    injectiveMoment H raw8052step0 = injectiveMoment H raw8052step1 := by
      have hz : ∀ i, raw8052step0 i (permutation9 0) = 0 := by decide +kernel
      have heq : raw8052step1 = (fun i j => raw8052step0 i (permutation9 j.succ)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_column (by decide) H raw8052step0 permutation9 hz
    injectiveMoment H raw8052step1 = injectiveMoment H raw8052step2 := by
      have heq : raw8052step2 = (fun i j => raw8052step1 (permutation3 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8052step1 permutation3 permutation5
    _ = injectiveMoment H node56 := by rfl

def raw8053 : Matrix (Fin 3) (Fin 4) ℤ := ![![0, -2, -1, 3], ![0, 2, 2, -4], ![0, 0, -1, 1]]

def raw8053step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 0, 0], ![-2, 2, 0], ![-1, 2, -1], ![3, -4, 1]]

def raw8053step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 0, 0], ![2, -2, 0], ![1, -2, 1], ![-3, 4, -1]]

def raw8053step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![2, -2, 0], ![1, -2, 1], ![-3, 4, -1]]

def raw8053step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-1, -3, 4], ![0, 2, -2], ![1, 1, -2]]

theorem canonical8053 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw8053 = injectiveMoment H node52 := by
  calc
    injectiveMoment H raw8053 = injectiveMoment H raw8053step0 := by
      have heq : raw8053step0 = raw8053.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw8053).symm
    injectiveMoment H raw8053step0 = injectiveMoment H raw8053step1 := by
      have heq : raw8053step1 = -raw8053step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw8053step0).symm
    injectiveMoment H raw8053step1 = injectiveMoment H raw8053step2 := by
      have hz : ∀ j, raw8053step1 (permutation9 0) j = 0 := by decide +kernel
      have heq : raw8053step2 = (fun i j => raw8053step1 (permutation9 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw8053step1 permutation9 hz
    injectiveMoment H raw8053step2 = injectiveMoment H raw8053step3 := by
      have heq : raw8053step3 = (fun i j => raw8053step2 (permutation7 i) (permutation7 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8053step2 permutation7 permutation7
    _ = injectiveMoment H node52 := by rfl

def raw8054 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -2, 0, 2], ![-1, 0, -1, 2], ![0, 1, -1, 0], ![0, 1, 3, -4], ![1, 0, -1, 0]]

def raw8054step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, -2, 0, 2], ![0, 1, -1, 0], ![0, 1, 3, -4], ![1, 0, -1, 0]]

theorem canonical8054 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8054 = injectiveMoment H node2715 := by
  calc
    injectiveMoment H raw8054 = injectiveMoment H raw8054step0 := by
      have heq : raw8054step0 = (fun i j => raw8054 (permutation57 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8054 permutation57 permutation9
    _ = injectiveMoment H node2715 := by rfl

def raw8055 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -2, 0, 2], ![-1, 0, -1, 2], ![0, 1, 3, -4], ![1, 1, -2, 0]]

def raw8055step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 2, 0, -2], ![1, 0, 1, -2], ![0, -1, -3, 4], ![-1, -1, 2, 0]]

def raw8055step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 2, 0], ![0, -1, -3, 4], ![0, 2, 0, -2], ![1, 0, 1, -2]]

theorem canonical8055 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw8055 = injectiveMoment H node1155 := by
  calc
    injectiveMoment H raw8055 = injectiveMoment H raw8055step0 := by
      have heq : raw8055step0 = -raw8055 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw8055).symm
    injectiveMoment H raw8055step0 = injectiveMoment H raw8055step1 := by
      have heq : raw8055step1 = (fun i j => raw8055step0 (permutation31 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8055step0 permutation31 permutation9
    _ = injectiveMoment H node1155 := by rfl

def raw8056 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -2, 0, 2], ![-1, 0, -1, 2], ![0, 2, 2, -4], ![1, 0, -1, 0]]

def raw8056step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, -2, 2], ![0, 2, 2, -4], ![1, -1, 0, 0]]

theorem canonical8056 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8056 = injectiveMoment H node1037 := by
  calc
    injectiveMoment H raw8056 = injectiveMoment H raw8056step0 := by
      have heq : raw8056step0 = (fun i j => raw8056 (permutation15 i) (permutation11 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8056 permutation15 permutation11
    _ = injectiveMoment H node1037 := by rfl

def raw8057 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -2, 0, 2], ![-1, 0, 0, 1], ![0, 2, 2, -4], ![1, 0, -2, 1]]

def raw8057step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -1, 0, 1], ![-2, 0, 2, 0], ![0, 0, 2, -2], ![2, 1, -4, 1]]

def raw8057step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 1, 0, -1], ![2, 0, -2, 0], ![0, 0, -2, 2], ![-2, -1, 4, -1]]

def raw8057step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, -1, 4], ![0, 0, 2, -2], ![0, 2, 0, -2], ![1, 0, -1, 0]]

theorem canonical8057 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw8057 = injectiveMoment H node775 := by
  calc
    injectiveMoment H raw8057 = injectiveMoment H raw8057step0 := by
      have heq : raw8057step0 = raw8057.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw8057).symm
    injectiveMoment H raw8057step0 = injectiveMoment H raw8057step1 := by
      have heq : raw8057step1 = -raw8057step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw8057step0).symm
    injectiveMoment H raw8057step1 = injectiveMoment H raw8057step2 := by
      have heq : raw8057step2 = (fun i j => raw8057step1 (permutation32 i) (permutation16 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8057step1 permutation32 permutation16
    _ = injectiveMoment H node775 := by rfl

def raw8058 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -2, 0, 2], ![-1, 0, 1, 0], ![0, 0, 1, -1], ![0, 2, -2, 0], ![1, 0, 0, -1]]

def raw8058step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -2, 2, 0], ![0, 0, -1, 1], ![0, 2, 0, -2], ![1, 0, -1, 0]]

theorem canonical8058 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8058 = injectiveMoment H node2745 := by
  calc
    injectiveMoment H raw8058 = injectiveMoment H raw8058step0 := by
      have heq : raw8058step0 = (fun i j => raw8058 (permutation57 i) (permutation10 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8058 permutation57 permutation10
    _ = injectiveMoment H node2745 := by rfl

def raw8059 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -2, 0, 2], ![-1, 0, 2, -1], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, 0, 0, -1]]

def raw8059step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 2, -2, 0], ![1, -1, 0, 0]]

theorem canonical8059 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8059 = injectiveMoment H node2609 := by
  calc
    injectiveMoment H raw8059 = injectiveMoment H raw8059step0 := by
      have heq : raw8059step0 = (fun i j => raw8059 (permutation64 i) (permutation13 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8059 permutation64 permutation13
    _ = injectiveMoment H node2609 := by rfl

def raw8060 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -2, 0, 2], ![-1, 0, 2, -1], ![0, 2, 0, -2], ![1, 0, -2, 1]]

def raw8060step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 2, -1], ![0, -2, 0, 2], ![0, 2, 0, -2], ![1, 0, -2, 1]]

theorem canonical8060 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8060 = injectiveMoment H node1304 := by
  calc
    injectiveMoment H raw8060 = injectiveMoment H raw8060step0 := by
      have heq : raw8060step0 = (fun i j => raw8060 (permutation15 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8060 permutation15 permutation9
    _ = injectiveMoment H node1304 := by rfl

def raw8061 : Matrix (Fin 5) (Fin 4) ℤ := ![![0, -2, 0, 2], ![-1, 0, 3, -2], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, 0, -1, 0]]

def raw8061step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 2, -2, 0], ![1, 0, 0, -1]]

theorem canonical8061 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8061 = injectiveMoment H node2421 := by
  calc
    injectiveMoment H raw8061 = injectiveMoment H raw8061step0 := by
      have heq : raw8061step0 = (fun i j => raw8061 (permutation64 i) (permutation13 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8061 permutation64 permutation13
    _ = injectiveMoment H node2421 := by rfl

def raw8062 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -2, 0, 2], ![-1, 1, -2, 2], ![0, 1, 3, -4], ![1, 0, -1, 0]]

def raw8062step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -1, 0, 1], ![-2, 1, 1, 0], ![0, -2, 3, -1], ![2, 2, -4, 0]]

def raw8062step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![0, -2, 1, 1], ![0, 2, 2, -4], ![1, 0, -1, 0]]

theorem canonical8062 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8062 = injectiveMoment H node1189 := by
  calc
    injectiveMoment H raw8062 = injectiveMoment H raw8062step0 := by
      have heq : raw8062step0 = raw8062.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw8062).symm
    injectiveMoment H raw8062step0 = injectiveMoment H raw8062step1 := by
      have heq : raw8062step1 = (fun i j => raw8062step0 (permutation24 i) (permutation27 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8062step0 permutation24 permutation27
    _ = injectiveMoment H node1189 := by rfl

def raw8063 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, -2, 0, 2], ![-1, 1, -1, 1], ![0, 1, -2, 1], ![1, 0, 3, -4]]

def raw8063step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![0, 2, 0, -2], ![1, -1, 1, -1], ![0, -1, 2, -1], ![-1, 0, -3, 4]]

def raw8063step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -3, 4], ![0, -1, 2, -1], ![0, 2, 0, -2], ![1, -1, 1, -1]]

theorem canonical8063 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw8063 = injectiveMoment H node1173 := by
  calc
    injectiveMoment H raw8063 = injectiveMoment H raw8063step0 := by
      have heq : raw8063step0 = -raw8063 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw8063).symm
    injectiveMoment H raw8063step0 = injectiveMoment H raw8063step1 := by
      have heq : raw8063step1 = (fun i j => raw8063step0 (permutation31 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8063step0 permutation31 permutation9
    _ = injectiveMoment H node1173 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
