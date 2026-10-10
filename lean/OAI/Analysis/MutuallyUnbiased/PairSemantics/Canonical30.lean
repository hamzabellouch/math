import OAI.Analysis.MutuallyUnbiased.PairSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes0
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes6
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes11
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes13
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes18
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes19
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes22
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes37

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw960 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, -3, 5], ![0, 4, -4], ![2, -1, -1]]

theorem canonical960 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw960 = injectiveMoment H node29 := by
  rfl

def raw961 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, -3, 5], ![1, -1, 0], ![1, 4, -5]]

def raw961step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 1, 1], ![-3, -1, 4], ![5, 0, -5]]

def raw961step1 : Matrix (Fin 3) (Fin 3) ℤ := ![![-1, -3, 4], ![0, 5, -5], ![1, -2, 1]]

theorem canonical961 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw961 = injectiveMoment H node55 := by
  calc
    injectiveMoment H raw961 = injectiveMoment H raw961step0 := by
      have heq : raw961step0 = raw961.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw961).symm
    injectiveMoment H raw961step0 = injectiveMoment H raw961step1 := by
      have heq : raw961step1 = (fun i j => raw961step0 (permutation6 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw961step0 permutation6 permutation5
    _ = injectiveMoment H node55 := by rfl

def raw962 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, -3, 5], ![1, 0, -1], ![1, 3, -4]]

def raw962step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 1, 1], ![-3, 0, 3], ![5, -1, -4]]

def raw962step1 : Matrix (Fin 3) (Fin 3) ℤ := ![![-1, -4, 5], ![0, 3, -3], ![1, 1, -2]]

theorem canonical962 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw962 = injectiveMoment H node49 := by
  calc
    injectiveMoment H raw962 = injectiveMoment H raw962step0 := by
      have heq : raw962step0 = raw962.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw962).symm
    injectiveMoment H raw962step0 = injectiveMoment H raw962step1 := by
      have heq : raw962step1 = (fun i j => raw962step0 (permutation8 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw962step0 permutation8 permutation6
    _ = injectiveMoment H node49 := by rfl

def raw963 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, -3, 5], ![1, 1, -2], ![1, 2, -3]]

theorem canonical963 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw963 = injectiveMoment H node30 := by
  rfl

def raw964 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, -3, 5], ![1, 2, -3], ![1, 1, -2]]

def raw964step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, -3, 5], ![1, 1, -2], ![1, 2, -3]]

theorem canonical964 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw964 = injectiveMoment H node30 := by
  calc
    injectiveMoment H raw964 = injectiveMoment H raw964step0 := by
      have heq : raw964step0 = (fun i j => raw964 (permutation4 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw964 permutation4 permutation3
    _ = injectiveMoment H node30 := by rfl

def raw965 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, -3, 5], ![1, 3, -4], ![1, 0, -1]]

def raw965step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 1, 1], ![-3, 3, 0], ![5, -4, -1]]

def raw965step1 : Matrix (Fin 3) (Fin 3) ℤ := ![![-1, -4, 5], ![0, 3, -3], ![1, 1, -2]]

theorem canonical965 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw965 = injectiveMoment H node49 := by
  calc
    injectiveMoment H raw965 = injectiveMoment H raw965step0 := by
      have heq : raw965step0 = raw965.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw965).symm
    injectiveMoment H raw965step0 = injectiveMoment H raw965step1 := by
      have heq : raw965step1 = (fun i j => raw965step0 (permutation8 i) (permutation8 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw965step0 permutation8 permutation8
    _ = injectiveMoment H node49 := by rfl

def raw966 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, -1, 5], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![2, 1, 0, -3]]

theorem canonical966 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw966 = injectiveMoment H node1439 := by
  rfl

def raw967 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, -1, 5], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![2, 1, -1, -2]]

theorem canonical967 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw967 = injectiveMoment H node1440 := by
  rfl

def raw968 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, -1, 5], ![0, 0, 1, -1], ![0, 0, 1, -1], ![1, 0, -1, 0], ![1, 2, 0, -3]]

def raw968step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, -1, 5], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, -1, 0], ![2, 1, 0, -3]]

theorem canonical968 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw968 = injectiveMoment H node1439 := by
  calc
    injectiveMoment H raw968 = injectiveMoment H raw968step0 := by
      have heq : raw968step0 = (fun i j => raw968 (permutation33 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw968 permutation33 permutation15
    _ = injectiveMoment H node1439 := by rfl

def raw969 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, -1, 5], ![0, 0, 1, -1], ![0, 0, 1, -1], ![1, 0, 0, -1], ![1, 2, -1, -2]]

def raw969step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, -1, 5], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 1, 0, -1], ![2, 1, -1, -2]]

theorem canonical969 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw969 = injectiveMoment H node1440 := by
  calc
    injectiveMoment H raw969 = injectiveMoment H raw969step0 := by
      have heq : raw969step0 = (fun i j => raw969 (permutation33 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw969 permutation33 permutation15
    _ = injectiveMoment H node1440 := by rfl

def raw970 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, -1, 5], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![2, 0, 1, -3]]

theorem canonical970 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw970 = injectiveMoment H node1441 := by
  rfl

def raw971 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, -1, 5], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, 1, -2], ![2, 0, 0, -2]]

theorem canonical971 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw971 = injectiveMoment H node1442 := by
  rfl

def raw972 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, -1, 5], ![0, 0, 1, -1], ![0, 1, -1, 0], ![1, 0, 0, -1], ![1, 1, 1, -3]]

theorem canonical972 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw972 = injectiveMoment H node1443 := by
  rfl

def raw973 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, -1, 5], ![0, 0, 1, -1], ![0, 1, -1, 0], ![1, 0, 1, -2], ![1, 1, 0, -2]]

theorem canonical973 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw973 = injectiveMoment H node1444 := by
  rfl

def raw974 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -2, -1, 5], ![0, 0, 1, -1], ![0, 1, -1, 0], ![2, 1, 1, -4]]

def raw974step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![-2, 0, 1, 1], ![-1, 1, -1, 1], ![5, -1, 0, -4]]

def raw974step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -4, 5], ![0, 0, 2, -2], ![0, 1, 1, -2], ![1, -1, 1, -1]]

theorem canonical974 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw974 = injectiveMoment H node1161 := by
  calc
    injectiveMoment H raw974 = injectiveMoment H raw974step0 := by
      have heq : raw974step0 = raw974.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw974).symm
    injectiveMoment H raw974step0 = injectiveMoment H raw974step1 := by
      have heq : raw974step1 = (fun i j => raw974step0 (permutation27 i) (permutation18 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw974step0 permutation27 permutation18
    _ = injectiveMoment H node1161 := by rfl

def raw975 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, -1, 5], ![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 1, 0, -1], ![2, 0, 0, -2]]

def raw975step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -2, -2, 5], ![0, 0, 1, -1], ![0, 0, 1, -1], ![0, 2, 0, -2], ![1, 0, 0, -1]]

theorem canonical975 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw975 = injectiveMoment H node2386 := by
  calc
    injectiveMoment H raw975 = injectiveMoment H raw975step0 := by
      have heq : raw975step0 = (fun i j => raw975 (permutation42 i) (permutation21 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw975 permutation42 permutation21
    _ = injectiveMoment H node2386 := by rfl

def raw976 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, -1, 5], ![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 1, 1, -2], ![2, 0, -1, -1]]

theorem canonical976 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw976 = injectiveMoment H node1445 := by
  rfl

def raw977 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, -1, 5], ![0, 0, 1, -1], ![0, 1, 0, -1], ![1, 0, 0, -1], ![1, 1, 0, -2]]

def raw977step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -2, -2, 5], ![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 1, 1, -2], ![1, 0, 0, -1]]

theorem canonical977 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw977 = injectiveMoment H node2387 := by
  calc
    injectiveMoment H raw977 = injectiveMoment H raw977step0 := by
      have heq : raw977step0 = (fun i j => raw977 (permutation42 i) (permutation21 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw977 permutation42 permutation21
    _ = injectiveMoment H node2387 := by rfl

def raw978 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -2, -1, 5], ![0, 0, 1, -1], ![0, 1, 0, -1], ![2, 1, 0, -3]]

def raw978step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![-2, 0, 1, 1], ![-1, 1, 0, 0], ![5, -1, -1, -3]]

def raw978step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, -3, 5], ![0, 0, 2, -2], ![0, 1, 0, -1], ![1, 0, 1, -2]]

theorem canonical978 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw978 = injectiveMoment H node890 := by
  calc
    injectiveMoment H raw978 = injectiveMoment H raw978step0 := by
      have heq : raw978step0 = raw978.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw978).symm
    injectiveMoment H raw978step0 = injectiveMoment H raw978step1 := by
      have heq : raw978step1 = (fun i j => raw978step0 (permutation28 i) (permutation24 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw978step0 permutation28 permutation24
    _ = injectiveMoment H node890 := by rfl

def raw979 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, -1, 5], ![0, 0, 1, -1], ![0, 1, 1, -2], ![0, 1, 0, -1], ![2, 0, -1, -1]]

def raw979step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, -1, 5], ![0, 0, 1, -1], ![0, 1, 0, -1], ![0, 1, 1, -2], ![2, 0, -1, -1]]

theorem canonical979 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw979 = injectiveMoment H node1445 := by
  calc
    injectiveMoment H raw979 = injectiveMoment H raw979step0 := by
      have heq : raw979step0 = (fun i j => raw979 (permutation35 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw979 permutation35 permutation9
    _ = injectiveMoment H node1445 := by rfl

def raw980 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -2, -1, 5], ![0, 0, 1, -1], ![0, 1, 1, -2], ![2, 1, -1, -2]]

def raw980step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![-2, 0, 1, 1], ![-1, 1, 1, -1], ![5, -1, -2, -2]]

def raw980step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, -2, 5], ![0, 0, 2, -2], ![0, 1, 1, -2], ![1, 1, -1, -1]]

theorem canonical980 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw980 = injectiveMoment H node752 := by
  calc
    injectiveMoment H raw980 = injectiveMoment H raw980step0 := by
      have heq : raw980step0 = raw980.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw980).symm
    injectiveMoment H raw980step0 = injectiveMoment H raw980step1 := by
      have heq : raw980step1 = (fun i j => raw980step0 (permutation27 i) (permutation18 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw980step0 permutation27 permutation18
    _ = injectiveMoment H node752 := by rfl

def raw981 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, -1, 5], ![0, 0, 1, -1], ![0, 2, 1, -3], ![1, 0, -1, 0], ![1, 0, 0, -1]]

def raw981step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, -1, 5], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, 0, -1], ![2, 0, 1, -3]]

theorem canonical981 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw981 = injectiveMoment H node1441 := by
  calc
    injectiveMoment H raw981 = injectiveMoment H raw981step0 := by
      have heq : raw981step0 = (fun i j => raw981 (permutation36 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw981 permutation36 permutation15
    _ = injectiveMoment H node1441 := by rfl

def raw982 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, -1, 5], ![0, 0, 2, -2], ![0, 1, -1, 0], ![0, 1, 0, -1], ![2, 0, 0, -2]]

theorem canonical982 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw982 = injectiveMoment H node1446 := by
  rfl

def raw983 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, -1, 5], ![0, 0, 2, -2], ![0, 1, -1, 0], ![1, 0, 0, -1], ![1, 1, 0, -2]]

theorem canonical983 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw983 = injectiveMoment H node1447 := by
  rfl

def raw984 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -2, -1, 5], ![0, 0, 2, -2], ![0, 1, -1, 0], ![2, 1, 0, -3]]

def raw984step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![-2, 0, 1, 1], ![-1, 2, -1, 0], ![5, -2, 0, -3]]

def raw984step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, 0, -2], ![2, 0, -1, -1], ![1, -2, 1, 0], ![-5, 2, 0, 3]]

def raw984step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -1, 2], ![0, 0, -2, 2], ![0, 2, 3, -5], ![1, -2, 0, 1]]

theorem canonical984 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw984 = injectiveMoment H node1258 := by
  calc
    injectiveMoment H raw984 = injectiveMoment H raw984step0 := by
      have heq : raw984step0 = raw984.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw984).symm
    injectiveMoment H raw984step0 = injectiveMoment H raw984step1 := by
      have heq : raw984step1 = -raw984step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw984step0).symm
    injectiveMoment H raw984step1 = injectiveMoment H raw984step2 := by
      have heq : raw984step2 = (fun i j => raw984step1 (permutation16 i) (permutation24 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw984step1 permutation16 permutation24
    _ = injectiveMoment H node1258 := by rfl

def raw985 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, -1, 5], ![0, 0, 2, -2], ![0, 1, 0, -1], ![0, 1, 0, -1], ![2, 0, -1, -1]]

theorem canonical985 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw985 = injectiveMoment H node1448 := by
  rfl

def raw986 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, -1, 5], ![0, 0, 2, -2], ![0, 1, 0, -1], ![1, 0, 0, -1], ![1, 1, -1, -1]]

theorem canonical986 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw986 = injectiveMoment H node1449 := by
  rfl

def raw987 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, -1, 5], ![0, 0, 2, -2], ![0, 1, 0, -1], ![1, 1, -1, -1], ![1, 0, 0, -1]]

def raw987step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, -1, 5], ![0, 0, 2, -2], ![0, 1, 0, -1], ![1, 0, 0, -1], ![1, 1, -1, -1]]

theorem canonical987 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw987 = injectiveMoment H node1449 := by
  calc
    injectiveMoment H raw987 = injectiveMoment H raw987step0 := by
      have heq : raw987step0 = (fun i j => raw987 (permutation34 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw987 permutation34 permutation9
    _ = injectiveMoment H node1449 := by rfl

def raw988 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -2, -1, 5], ![0, 0, 2, -2], ![0, 1, 0, -1], ![2, 1, -1, -2]]

def raw988step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![-2, 0, 1, 1], ![-1, 2, 0, -1], ![5, -2, -1, -2]]

def raw988step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, -2, 5], ![0, 0, 2, -2], ![0, 2, -1, -1], ![1, 0, 1, -2]]

theorem canonical988 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw988 = injectiveMoment H node753 := by
  calc
    injectiveMoment H raw988 = injectiveMoment H raw988step0 := by
      have heq : raw988step0 = raw988.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw988).symm
    injectiveMoment H raw988step0 = injectiveMoment H raw988step1 := by
      have heq : raw988step1 = (fun i j => raw988step0 (permutation28 i) (permutation24 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw988step0 permutation28 permutation24
    _ = injectiveMoment H node753 := by rfl

def raw989 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, -1, 5], ![0, 0, 2, -2], ![0, 2, -1, -1], ![1, 0, 0, -1], ![1, 0, 0, -1]]

def raw989step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -2, -1, 5], ![0, 0, 2, -2], ![0, 1, 0, -1], ![0, 1, 0, -1], ![2, 0, -1, -1]]

theorem canonical989 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw989 = injectiveMoment H node1448 := by
  calc
    injectiveMoment H raw989 = injectiveMoment H raw989step0 := by
      have heq : raw989step0 = (fun i j => raw989 (permutation36 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw989 permutation36 permutation15
    _ = injectiveMoment H node1448 := by rfl

def raw990 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -2, -1, 5], ![0, 0, 2, -2], ![0, 2, -1, -1], ![2, 0, 0, -2]]

theorem canonical990 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw990 = injectiveMoment H node391 := by
  rfl

def raw991 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -2, -1, 5], ![0, 0, 2, -2], ![0, 2, 0, -2], ![2, 0, -1, -1]]

def raw991step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -2, -1, 5], ![0, 0, 2, -2], ![0, 2, -1, -1], ![2, 0, 0, -2]]

theorem canonical991 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw991 = injectiveMoment H node391 := by
  calc
    injectiveMoment H raw991 = injectiveMoment H raw991step0 := by
      have heq : raw991step0 = (fun i j => raw991 (permutation10 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw991 permutation10 permutation15
    _ = injectiveMoment H node391 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
