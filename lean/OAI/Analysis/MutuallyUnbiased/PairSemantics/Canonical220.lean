import OAI.Analysis.MutuallyUnbiased.PairSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes1
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes2
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes3
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes12
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes14
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes15
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes16
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes17
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes18
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes20
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes21
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes26
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes42
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes43

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw7040 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 0, -3, 4], ![1, -2, 3, -2], ![0, 2, 0, -2]]

def raw7040step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 1, 0], ![0, -2, 2], ![-3, 3, 0], ![4, -2, -2]]

def raw7040step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 1, -1], ![0, 3, -3], ![2, -2, 0]]

theorem canonical7040 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7040 = injectiveMoment H node147 := by
  calc
    injectiveMoment H raw7040 = injectiveMoment H raw7040step0 := by
      have heq : raw7040step0 = raw7040.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw7040).symm
    injectiveMoment H raw7040step0 = injectiveMoment H raw7040step1 := by
      have heq : raw7040step1 = (fun i j => raw7040step0 (permutation28 i) (permutation8 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7040step0 permutation28 permutation8
    _ = injectiveMoment H node147 := by rfl

def raw7041 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 0, -3, 4], ![1, -1, 2, -2], ![0, 1, 1, -2]]

def raw7041step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 1, 0], ![0, -1, 1], ![-3, 2, 1], ![4, -2, -2]]

def raw7041step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 1, -1], ![1, -1, 0], ![1, 2, -3]]

theorem canonical7041 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7041 = injectiveMoment H node149 := by
  calc
    injectiveMoment H raw7041 = injectiveMoment H raw7041step0 := by
      have heq : raw7041step0 = raw7041.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw7041).symm
    injectiveMoment H raw7041step0 = injectiveMoment H raw7041step1 := by
      have heq : raw7041step1 = (fun i j => raw7041step0 (permutation27 i) (permutation8 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7041step0 permutation27 permutation8
    _ = injectiveMoment H node149 := by rfl

def raw7042 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![-1, -1, 2, 0], ![1, 0, 1, -2], ![1, 1, -1, -1]]

def raw7042step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, -1, 3, -2], ![0, 1, -2, 1], ![1, 1, -1, -1]]

theorem canonical7042 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7042 = injectiveMoment H node1013 := by
  calc
    injectiveMoment H raw7042 = injectiveMoment H raw7042step0 := by
      have heq : raw7042step0 = (fun i j => raw7042 (permutation15 i) (permutation16 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7042 permutation15 permutation16
    _ = injectiveMoment H node1013 := by rfl

def raw7043 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![-1, 0, 2, -1], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, 0, 1, -2]]

def raw7043step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![1, 0, 2, -3], ![1, 0, -2, 1], ![0, -1, 1, 0], ![-1, 1, 0, 0], ![-1, 0, -1, 2]]

def raw7043step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -1, 2, -1], ![0, 1, -3, 2], ![0, 1, 1, -2], ![1, -1, 0, 0]]

theorem canonical7043 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw7043 = injectiveMoment H node2777 := by
  calc
    injectiveMoment H raw7043 = injectiveMoment H raw7043step0 := by
      have heq : raw7043step0 = -raw7043 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw7043).symm
    injectiveMoment H raw7043step0 = injectiveMoment H raw7043step1 := by
      have heq : raw7043step1 = (fun i j => raw7043step0 (permutation98 i) (permutation16 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7043step0 permutation98 permutation16
    _ = injectiveMoment H node2777 := by rfl

def raw7044 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![-1, 0, 2, -1], ![0, 1, -1, 0], ![1, -1, 1, -1], ![1, 0, 0, -1]]

def raw7044step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![1, 0, 2, -3], ![1, 0, -2, 1], ![0, -1, 1, 0], ![-1, 1, -1, 1], ![-1, 0, 0, 1]]

def raw7044step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -1, 1, 0], ![0, 1, -3, 2], ![0, 1, 1, -2], ![1, -1, 1, -1]]

theorem canonical7044 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw7044 = injectiveMoment H node2772 := by
  calc
    injectiveMoment H raw7044 = injectiveMoment H raw7044step0 := by
      have heq : raw7044step0 = -raw7044 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw7044).symm
    injectiveMoment H raw7044step0 = injectiveMoment H raw7044step1 := by
      have heq : raw7044step1 = (fun i j => raw7044step0 (permutation98 i) (permutation16 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7044step0 permutation98 permutation16
    _ = injectiveMoment H node2772 := by rfl

def raw7045 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![-1, 0, 2, -1], ![0, 1, 0, -1], ![1, -1, 1, -1], ![1, 0, -1, 0]]

def raw7045step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![1, 0, 2, -3], ![1, 0, -2, 1], ![0, -1, 0, 1], ![-1, 1, -1, 1], ![-1, 0, 1, 0]]

def raw7045step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -1, 1, 0], ![0, 1, -2, 1], ![0, 1, 2, -3], ![1, -1, -1, 1]]

theorem canonical7045 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw7045 = injectiveMoment H node2774 := by
  calc
    injectiveMoment H raw7045 = injectiveMoment H raw7045step0 := by
      have heq : raw7045step0 = -raw7045 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw7045).symm
    injectiveMoment H raw7045step0 = injectiveMoment H raw7045step1 := by
      have heq : raw7045step1 = (fun i j => raw7045step0 (permutation100 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7045step0 permutation100 permutation15
    _ = injectiveMoment H node2774 := by rfl

def raw7046 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![-1, 0, 2, -1], ![0, 1, 1, -2], ![1, -1, 0, 0], ![1, 0, -1, 0]]

def raw7046step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![1, 0, 2, -3], ![1, 0, -2, 1], ![0, -1, -1, 2], ![-1, 1, 0, 0], ![-1, 0, 1, 0]]

def raw7046step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, -1, 1, 0], ![0, 1, -2, 1], ![0, 1, 2, -3], ![1, -1, 0, 0]]

theorem canonical7046 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw7046 = injectiveMoment H node2726 := by
  calc
    injectiveMoment H raw7046 = injectiveMoment H raw7046step0 := by
      have heq : raw7046step0 = -raw7046 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw7046).symm
    injectiveMoment H raw7046step0 = injectiveMoment H raw7046step1 := by
      have heq : raw7046step1 = (fun i j => raw7046step0 (permutation100 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7046step0 permutation100 permutation15
    _ = injectiveMoment H node2726 := by rfl

def raw7047 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![-1, 0, 2, -1], ![1, -1, 1, -1], ![1, 1, -1, -1]]

def raw7047step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![1, 0, 2, -3], ![1, 0, -2, 1], ![-1, 1, -1, 1], ![-1, -1, 1, 1]]

def raw7047step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, 1, -3, 2], ![0, 1, 1, -2], ![1, -1, 1, -1]]

theorem canonical7047 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw7047 = injectiveMoment H node1123 := by
  calc
    injectiveMoment H raw7047 = injectiveMoment H raw7047step0 := by
      have heq : raw7047step0 = -raw7047 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw7047).symm
    injectiveMoment H raw7047step0 = injectiveMoment H raw7047step1 := by
      have heq : raw7047step1 = (fun i j => raw7047step0 (permutation27 i) (permutation16 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7047step0 permutation27 permutation16
    _ = injectiveMoment H node1123 := by rfl

def raw7048 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![-1, 0, 3, -2], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, 0, 0, -1]]

def raw7048step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![1, 0, 2, -3], ![1, 0, -3, 2], ![0, -1, 1, 0], ![-1, 1, 0, 0], ![-1, 0, 0, 1]]

def raw7048step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -1, 1, 0], ![0, 1, -3, 2], ![0, 1, 2, -3], ![1, -1, 0, 0]]

theorem canonical7048 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw7048 = injectiveMoment H node2773 := by
  calc
    injectiveMoment H raw7048 = injectiveMoment H raw7048step0 := by
      have heq : raw7048step0 = -raw7048 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw7048).symm
    injectiveMoment H raw7048step0 = injectiveMoment H raw7048step1 := by
      have heq : raw7048step1 = (fun i j => raw7048step0 (permutation98 i) (permutation16 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7048step0 permutation98 permutation16
    _ = injectiveMoment H node2773 := by rfl

def raw7049 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![-1, 0, 3, -2], ![0, 1, 0, -1], ![1, -1, -1, 1], ![1, 0, 0, -1]]

def raw7049step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![1, 0, 2, -3], ![1, 0, -3, 2], ![0, -1, 0, 1], ![-1, 1, 1, -1], ![-1, 0, 0, 1]]

def raw7049step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -1, 0, 1], ![0, 1, -3, 2], ![0, 1, 2, -3], ![1, -1, 1, -1]]

theorem canonical7049 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw7049 = injectiveMoment H node2765 := by
  calc
    injectiveMoment H raw7049 = injectiveMoment H raw7049step0 := by
      have heq : raw7049step0 = -raw7049 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw7049).symm
    injectiveMoment H raw7049step0 = injectiveMoment H raw7049step1 := by
      have heq : raw7049step1 = (fun i j => raw7049step0 (permutation100 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7049step0 permutation100 permutation15
    _ = injectiveMoment H node2765 := by rfl

def raw7050 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![-1, 0, 3, -2], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 0, -1, 0]]

def raw7050step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![1, 0, 2, -3], ![1, 0, -3, 2], ![0, -1, 0, 1], ![-1, 1, 0, 0], ![-1, 0, 1, 0]]

def raw7050step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -1, 1, 0], ![0, 1, -3, 2], ![0, 1, 2, -3], ![1, -1, 0, 0]]

theorem canonical7050 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw7050 = injectiveMoment H node2773 := by
  calc
    injectiveMoment H raw7050 = injectiveMoment H raw7050step0 := by
      have heq : raw7050step0 = -raw7050 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw7050).symm
    injectiveMoment H raw7050step0 = injectiveMoment H raw7050step1 := by
      have heq : raw7050step1 = (fun i j => raw7050step0 (permutation100 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7050step0 permutation100 permutation15
    _ = injectiveMoment H node2773 := by rfl

def raw7051 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![-1, 0, 3, -2], ![1, -1, 0, 0], ![1, 1, -1, -1]]

def raw7051step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![1, 0, 2, -3], ![1, 0, -3, 2], ![-1, 1, 0, 0], ![-1, -1, 1, 1]]

def raw7051step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, 1, -3, 2], ![0, 1, 2, -3], ![1, -1, 0, 0]]

theorem canonical7051 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw7051 = injectiveMoment H node1124 := by
  calc
    injectiveMoment H raw7051 = injectiveMoment H raw7051step0 := by
      have heq : raw7051step0 = -raw7051 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw7051).symm
    injectiveMoment H raw7051step0 = injectiveMoment H raw7051step1 := by
      have heq : raw7051step1 = (fun i j => raw7051step0 (permutation29 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7051step0 permutation29 permutation15
    _ = injectiveMoment H node1124 := by rfl

def raw7052 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![-1, 1, -1, 1], ![1, -1, 0, 0], ![1, 0, 3, -4]]

def raw7052step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 1, 0, 0], ![0, -1, -2, 3], ![0, 1, 3, -4], ![1, -1, -1, 1]]

theorem canonical7052 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7052 = injectiveMoment H node1354 := by
  calc
    injectiveMoment H raw7052 = injectiveMoment H raw7052step0 := by
      have heq : raw7052step0 = (fun i j => raw7052 (permutation22 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7052 permutation22 permutation15
    _ = injectiveMoment H node1354 := by rfl

def raw7053 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![-1, 1, -1, 1], ![1, -1, 3, -3], ![1, 0, 0, -1]]

def raw7053step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![1, 0, 2, -3], ![1, -1, 1, -1], ![-1, 1, -3, 3], ![-1, 0, 0, 1]]

def raw7053step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 1, 1, -1], ![0, -1, 0, 1], ![0, 1, 2, -3], ![1, -1, -3, 3]]

theorem canonical7053 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw7053 = injectiveMoment H node1363 := by
  calc
    injectiveMoment H raw7053 = injectiveMoment H raw7053step0 := by
      have heq : raw7053step0 = -raw7053 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw7053).symm
    injectiveMoment H raw7053step0 = injectiveMoment H raw7053step1 := by
      have heq : raw7053step1 = (fun i j => raw7053step0 (permutation19 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7053step0 permutation19 permutation15
    _ = injectiveMoment H node1363 := by rfl

def raw7054 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![-1, 1, 1, -1], ![0, 1, 1, -2], ![1, -1, 0, 0], ![1, -1, 0, 0]]

def raw7054step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, -1, 1, -1], ![1, 0, 1, -2]]

theorem canonical7054 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7054 = injectiveMoment H node1715 := by
  calc
    injectiveMoment H raw7054 = injectiveMoment H raw7054step0 := by
      have heq : raw7054step0 = (fun i j => raw7054 (permutation49 i) (permutation21 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7054 permutation49 permutation21
    _ = injectiveMoment H node1715 := by rfl

def raw7055 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![-1, 1, 1, -1], ![1, -1, 2, -2], ![1, 0, -1, 0]]

def raw7055step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 1, -2, 2], ![0, -1, 3, -2], ![0, 1, 0, -1], ![1, -1, -1, 1]]

theorem canonical7055 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7055 = injectiveMoment H node1334 := by
  calc
    injectiveMoment H raw7055 = injectiveMoment H raw7055step0 := by
      have heq : raw7055step0 = (fun i j => raw7055 (permutation22 i) (permutation16 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7055 permutation22 permutation16
    _ = injectiveMoment H node1334 := by rfl

def raw7056 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![-1, 1, 3, -3], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, -1, 0, 0]]

theorem canonical7056 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7056 = injectiveMoment H node2695 := by
  rfl

def raw7057 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![-1, 1, 3, -3], ![1, -1, 0, 0], ![1, 0, -1, 0]]

def raw7057step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, 1, -1, 0], ![-2, 3, 0, -1], ![3, -3, 0, 0]]

def raw7057step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![1, 1, -1, -1], ![0, -1, 1, 0], ![2, -3, 0, 1], ![-3, 3, 0, 0]]

def raw7057step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, 0, -3, 3], ![0, 1, 0, -1], ![1, 0, 2, -3]]

theorem canonical7057 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw7057 = injectiveMoment H node1103 := by
  calc
    injectiveMoment H raw7057 = injectiveMoment H raw7057step0 := by
      have heq : raw7057step0 = raw7057.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw7057).symm
    injectiveMoment H raw7057step0 = injectiveMoment H raw7057step1 := by
      have heq : raw7057step1 = -raw7057step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw7057step0).symm
    injectiveMoment H raw7057step1 = injectiveMoment H raw7057step2 := by
      have heq : raw7057step2 = (fun i j => raw7057step1 (permutation13 i) (permutation31 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7057step1 permutation13 permutation31
    _ = injectiveMoment H node1103 := by rfl

def raw7058 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![-1, 1, 3, -3], ![1, 0, -1, 0], ![1, -1, 0, 0]]

def raw7058step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, 1, 0, -1], ![-2, 3, -1, 0], ![3, -3, 0, 0]]

def raw7058step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![1, 1, -1, -1], ![0, -1, 0, 1], ![2, -3, 1, 0], ![-3, 3, 0, 0]]

def raw7058step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, 0, -3, 3], ![0, 1, 0, -1], ![1, 0, 2, -3]]

theorem canonical7058 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw7058 = injectiveMoment H node1103 := by
  calc
    injectiveMoment H raw7058 = injectiveMoment H raw7058step0 := by
      have heq : raw7058step0 = raw7058.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw7058).symm
    injectiveMoment H raw7058step0 = injectiveMoment H raw7058step1 := by
      have heq : raw7058step1 = -raw7058step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw7058step0).symm
    injectiveMoment H raw7058step1 = injectiveMoment H raw7058step2 := by
      have heq : raw7058step2 = (fun i j => raw7058step1 (permutation13 i) (permutation25 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7058step1 permutation13 permutation25
    _ = injectiveMoment H node1103 := by rfl

def raw7059 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![-1, 2, 2, -3], ![1, -1, 0, 0], ![1, -1, 0, 0]]

def raw7059step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, 2, -1, -1], ![-2, 2, 0, 0], ![3, -3, 0, 0]]

def raw7059step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, -2, 2], ![0, 0, 3, -3], ![1, 1, -1, -1]]

theorem canonical7059 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7059 = injectiveMoment H node1028 := by
  calc
    injectiveMoment H raw7059 = injectiveMoment H raw7059step0 := by
      have heq : raw7059step0 = raw7059.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw7059).symm
    injectiveMoment H raw7059step0 = injectiveMoment H raw7059step1 := by
      have heq : raw7059step1 = (fun i j => raw7059step0 (permutation18 i) (permutation25 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7059step0 permutation18 permutation25
    _ = injectiveMoment H node1028 := by rfl

def raw7060 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![0, -2, 1, 1], ![0, 2, 2, -4], ![1, 0, -1, 0]]

theorem canonical7060 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7060 = injectiveMoment H node1189 := by
  rfl

def raw7061 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![0, -2, 1, 1], ![1, 2, 1, -4]]

def raw7061step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -2, 2], ![-2, 1, 1], ![3, 1, -4]]

def raw7061step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![1, -2, 1], ![1, 3, -4]]

theorem canonical7061 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7061 = injectiveMoment H node206 := by
  calc
    injectiveMoment H raw7061 = injectiveMoment H raw7061step0 := by
      have heq : raw7061step0 = raw7061.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw7061).symm
    injectiveMoment H raw7061step0 = injectiveMoment H raw7061step1 := by
      have heq : raw7061step1 = (fun i j => raw7061step0 (permutation15 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7061step0 permutation15 permutation5
    _ = injectiveMoment H node206 := by rfl

def raw7062 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![0, -2, 2, 0], ![0, 0, 1, -1], ![0, 2, -1, -1], ![1, 0, 0, -1]]

theorem canonical7062 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7062 = injectiveMoment H node2696 := by
  rfl

def raw7063 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![0, -2, 2, 0], ![0, 0, 1, -1], ![0, 2, 0, -2], ![1, 0, -1, 0]]

theorem canonical7063 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7063 = injectiveMoment H node2697 := by
  rfl

def raw7064 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![0, -2, 2, 0], ![0, 2, -1, -1], ![1, 0, 1, -2]]

theorem canonical7064 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7064 = injectiveMoment H node1190 := by
  rfl

def raw7065 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![0, -2, 2, 0], ![0, 2, 0, -2], ![1, 0, 0, -1]]

def raw7065step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![0, 0, 2, -2], ![0, 2, -2, 0], ![1, 0, 0, -1]]

theorem canonical7065 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7065 = injectiveMoment H node806 := by
  calc
    injectiveMoment H raw7065 = injectiveMoment H raw7065step0 := by
      have heq : raw7065step0 = (fun i j => raw7065 (permutation11 i) (permutation11 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7065 permutation11 permutation11
    _ = injectiveMoment H node806 := by rfl

def raw7066 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![0, -2, 2, 0], ![0, 2, 1, -3], ![1, 0, -1, 0]]

theorem canonical7066 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7066 = injectiveMoment H node1191 := by
  rfl

def raw7067 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![0, -2, 2, 0], ![1, 2, 0, -3]]

def raw7067step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -2, 2], ![-2, 2, 0], ![3, 0, -3]]

def raw7067step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 3, -3], ![2, -2, 0]]

theorem canonical7067 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7067 = injectiveMoment H node204 := by
  calc
    injectiveMoment H raw7067 = injectiveMoment H raw7067step0 := by
      have heq : raw7067step0 = raw7067.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw7067).symm
    injectiveMoment H raw7067step0 = injectiveMoment H raw7067step1 := by
      have heq : raw7067step1 = (fun i j => raw7067step0 (permutation16 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7067step0 permutation16 permutation5
    _ = injectiveMoment H node204 := by rfl

def raw7068 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![0, -2, 3, -1], ![0, 1, 0, -1], ![1, 1, -1, -1]]

def raw7068step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -2, 1, 1], ![-2, 3, 0, -1], ![3, -1, -1, -1]]

def raw7068step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, -1, 3, -2], ![0, 1, 0, -1], ![1, 1, -2, 0]]

theorem canonical7068 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7068 = injectiveMoment H node950 := by
  calc
    injectiveMoment H raw7068 = injectiveMoment H raw7068step0 := by
      have heq : raw7068step0 = raw7068.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw7068).symm
    injectiveMoment H raw7068step0 = injectiveMoment H raw7068step1 := by
      have heq : raw7068step1 = (fun i j => raw7068step0 (permutation31 i) (permutation26 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7068step0 permutation31 permutation26
    _ = injectiveMoment H node950 := by rfl

def raw7069 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![0, -2, 3, -1], ![0, 2, -1, -1], ![1, 0, 0, -1]]

def raw7069step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 0, 1], ![0, -2, 2, 0], ![-2, 3, -1, 0], ![3, -1, -1, -1]]

def raw7069step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -1, 3], ![0, -1, 3, -2], ![0, 2, -2, 0], ![1, 0, 0, -1]]

theorem canonical7069 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7069 = injectiveMoment H node951 := by
  calc
    injectiveMoment H raw7069 = injectiveMoment H raw7069step0 := by
      have heq : raw7069step0 = raw7069.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw7069).symm
    injectiveMoment H raw7069step0 = injectiveMoment H raw7069step1 := by
      have heq : raw7069step1 = (fun i j => raw7069step0 (permutation32 i) (permutation32 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7069step0 permutation32 permutation32
    _ = injectiveMoment H node951 := by rfl

def raw7070 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![0, -2, 3, -1], ![0, 2, 0, -2], ![1, 0, -1, 0]]

theorem canonical7070 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7070 = injectiveMoment H node1193 := by
  rfl

def raw7071 : Matrix (Fin 3) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![0, -2, 3, -1], ![1, 2, -1, -2]]

def raw7071step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -2, 2], ![-2, 3, -1], ![3, -1, -2]]

def raw7071step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 0, -1], ![0, 2, -2], ![2, -3, 1], ![-3, 1, 2]]

def raw7071step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 2, -3], ![2, -2, 0]]

theorem canonical7071 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw7071 = injectiveMoment H node107 := by
  calc
    injectiveMoment H raw7071 = injectiveMoment H raw7071step0 := by
      have heq : raw7071step0 = raw7071.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw7071).symm
    injectiveMoment H raw7071step0 = injectiveMoment H raw7071step1 := by
      have heq : raw7071step1 = -raw7071step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw7071step0).symm
    injectiveMoment H raw7071step1 = injectiveMoment H raw7071step2 := by
      have heq : raw7071step2 = (fun i j => raw7071step1 (permutation22 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7071step1 permutation22 permutation6
    _ = injectiveMoment H node107 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
