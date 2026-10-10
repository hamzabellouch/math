import OAI.Analysis.MutuallyUnbiased.PairSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes7
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes12
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes16
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes17
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes18
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes20
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes25
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes26
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Nodes37

namespace OAI

namespace MUB6.Certificate.PairSemantics

def raw1984 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 1, -2, 1], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, 0, 3, -4]]

theorem canonical1984 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1984 = injectiveMoment H node1707 := by
  rfl

def raw1985 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 1, -2, 1], ![0, 1, -1, 0], ![1, -1, 1, -1], ![1, 0, 2, -3]]

theorem canonical1985 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1985 = injectiveMoment H node1708 := by
  rfl

def raw1986 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 1, -2, 1], ![0, 1, -1, 0], ![2, -1, 3, -4]]

def raw1986step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![-1, 1, 1, -1], ![0, -2, -1, 3], ![3, 1, 0, -4]]

def raw1986step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![0, 0, -2, 2], ![0, 1, 3, -4], ![1, 1, -1, -1]]

theorem canonical1986 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1986 = injectiveMoment H node792 := by
  calc
    injectiveMoment H raw1986 = injectiveMoment H raw1986step0 := by
      have heq : raw1986step0 = raw1986.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw1986).symm
    injectiveMoment H raw1986step0 = injectiveMoment H raw1986step1 := by
      have heq : raw1986step1 = (fun i j => raw1986step0 (permutation22 i) (permutation23 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1986step0 permutation22 permutation23
    _ = injectiveMoment H node792 := by rfl

def raw1987 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 1, -2, 1], ![0, 1, 0, -1], ![1, -1, 0, 0], ![1, 0, 2, -3]]

def raw1987step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, 1, 0, -3], ![0, -1, 2, -1], ![0, -1, 0, 1], ![-1, 1, 0, 0], ![-1, 0, -2, 3]]

def raw1987step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, -1, 1, 0], ![0, 0, -1, 1], ![0, 2, 1, -3], ![2, 0, -1, -1]]

theorem canonical1987 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw1987 = injectiveMoment H node1628 := by
  calc
    injectiveMoment H raw1987 = injectiveMoment H raw1987step0 := by
      have heq : raw1987step0 = -raw1987 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw1987).symm
    injectiveMoment H raw1987step0 = injectiveMoment H raw1987step1 := by
      have heq : raw1987step1 = (fun i j => raw1987step0 (permutation149 i) (permutation21 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1987step0 permutation149 permutation21
    _ = injectiveMoment H node1628 := by rfl

def raw1988 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 1, -2, 1], ![0, 1, 0, -1], ![1, -1, 1, -1], ![1, 0, 1, -2]]

theorem canonical1988 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1988 = injectiveMoment H node1709 := by
  rfl

def raw1989 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 1, -2, 1], ![0, 1, 0, -1], ![1, -1, 2, -2], ![1, 0, 0, -1]]

theorem canonical1989 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1989 = injectiveMoment H node1710 := by
  rfl

def raw1990 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 1, -2, 1], ![0, 1, 0, -1], ![2, -1, 2, -3]]

def raw1990step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![-1, 1, 1, -1], ![0, -2, 0, 2], ![3, 1, -1, -3]]

def raw1990step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, 0, -2], ![1, -1, -1, 1], ![0, 2, 0, -2], ![-3, -1, 1, 3]]

def raw1990step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 1, 1], ![0, 0, 2, -2], ![0, 2, 0, -2], ![1, -1, -3, 3]]

theorem canonical1990 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw1990 = injectiveMoment H node1120 := by
  calc
    injectiveMoment H raw1990 = injectiveMoment H raw1990step0 := by
      have heq : raw1990step0 = raw1990.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw1990).symm
    injectiveMoment H raw1990step0 = injectiveMoment H raw1990step1 := by
      have heq : raw1990step1 = -raw1990step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw1990step0).symm
    injectiveMoment H raw1990step1 = injectiveMoment H raw1990step2 := by
      have heq : raw1990step2 = (fun i j => raw1990step1 (permutation15 i) (permutation23 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1990step1 permutation15 permutation23
    _ = injectiveMoment H node1120 := by rfl

def raw1991 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 1, -2, 1], ![0, 1, 1, -2], ![1, -1, 1, -1], ![1, 0, 0, -1]]

theorem canonical1991 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1991 = injectiveMoment H node1711 := by
  rfl

def raw1992 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 1, -2, 1], ![0, 1, 1, -2], ![2, -1, 1, -2]]

theorem canonical1992 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1992 = injectiveMoment H node484 := by
  rfl

def raw1993 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 1, -2, 1], ![0, 1, 2, -3], ![1, -1, 0, 0], ![1, 0, 0, -1]]

def raw1993step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![2, 1, 0, -3], ![0, -1, 2, -1], ![0, -1, -2, 3], ![-1, 1, 0, 0], ![-1, 0, 0, 1]]

def raw1993step1 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 0, -1, 1], ![0, 1, -1, 0], ![0, 1, 2, -3], ![2, -1, 0, -1]]

theorem canonical1993 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw1993 = injectiveMoment H node1668 := by
  calc
    injectiveMoment H raw1993 = injectiveMoment H raw1993step0 := by
      have heq : raw1993step0 = -raw1993 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw1993).symm
    injectiveMoment H raw1993step0 = injectiveMoment H raw1993step1 := by
      have heq : raw1993step1 = (fun i j => raw1993step0 (permutation102 i) (permutation23 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1993step0 permutation102 permutation23
    _ = injectiveMoment H node1668 := by rfl

def raw1994 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 1, -2, 1], ![0, 1, 2, -3], ![1, -1, 1, -1], ![1, 0, -1, 0]]

theorem canonical1994 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1994 = injectiveMoment H node1712 := by
  rfl

def raw1995 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 1, -2, 1], ![0, 1, 2, -3], ![2, -1, 0, -1]]

theorem canonical1995 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1995 = injectiveMoment H node485 := by
  rfl

def raw1996 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 1, -2, 1], ![0, 1, 3, -4], ![1, -1, 0, 0], ![1, 0, -1, 0]]

theorem canonical1996 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1996 = injectiveMoment H node1713 := by
  rfl

def raw1997 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 1, -2, 1], ![0, 1, 3, -4], ![2, -1, -1, 0]]

theorem canonical1997 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1997 = injectiveMoment H node486 := by
  rfl

def raw1998 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 1, -2, 1], ![1, -1, 0, 0], ![1, 1, 2, -4]]

def raw1998step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![-1, 1, -1, 1], ![0, -2, 0, 2], ![3, 1, 0, -4]]

def raw1998step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![2, 0, -1, -1], ![1, -1, 1, -1], ![0, 2, 0, -2], ![-3, -1, 0, 4]]

def raw1998step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, 2, -1], ![0, -1, -3, 4], ![0, 2, 0, -2], ![1, -1, 1, -1]]

theorem canonical1998 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw1998 = injectiveMoment H node1306 := by
  calc
    injectiveMoment H raw1998 = injectiveMoment H raw1998step0 := by
      have heq : raw1998step0 = raw1998.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw1998).symm
    injectiveMoment H raw1998step0 = injectiveMoment H raw1998step1 := by
      have heq : raw1998step1 = -raw1998step0 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw1998step0).symm
    injectiveMoment H raw1998step1 = injectiveMoment H raw1998step2 := by
      have heq : raw1998step2 = (fun i j => raw1998step1 (permutation14 i) (permutation23 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw1998step1 permutation14 permutation23
    _ = injectiveMoment H node1306 := by rfl

def raw1999 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 1, -2, 1], ![1, -1, 1, -1], ![1, 1, 1, -3]]

theorem canonical1999 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw1999 = injectiveMoment H node487 := by
  rfl

def raw2000 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 1, -2, 1], ![1, -1, 2, -2], ![1, 1, 0, -2]]

theorem canonical2000 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2000 = injectiveMoment H node488 := by
  rfl

def raw2001 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 1, -2, 1], ![1, 0, -1, 0], ![1, 0, 3, -4]]

def raw2001step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![0, 1, -1, 0], ![0, 1, 3, -4], ![1, 0, -2, 1]]

theorem canonical2001 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2001 = injectiveMoment H node818 := by
  calc
    injectiveMoment H raw2001 = injectiveMoment H raw2001step0 := by
      have heq : raw2001step0 = (fun i j => raw2001 (permutation12 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2001 permutation12 permutation15
    _ = injectiveMoment H node818 := by rfl

def raw2002 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 1, -2, 1], ![1, 0, 0, -1], ![1, 0, 2, -3]]

def raw2002step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![0, 1, 0, -1], ![0, 1, 2, -3], ![1, 0, -2, 1]]

theorem canonical2002 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2002 = injectiveMoment H node819 := by
  calc
    injectiveMoment H raw2002 = injectiveMoment H raw2002step0 := by
      have heq : raw2002step0 = (fun i j => raw2002 (permutation12 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2002 permutation12 permutation15
    _ = injectiveMoment H node819 := by rfl

def raw2003 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 1, -2, 1], ![1, 0, 1, -2], ![1, 0, 1, -2]]

def raw2003step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![0, 1, 1, -2], ![0, 1, 1, -2], ![1, 0, -2, 1]]

theorem canonical2003 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2003 = injectiveMoment H node820 := by
  calc
    injectiveMoment H raw2003 = injectiveMoment H raw2003step0 := by
      have heq : raw2003step0 = (fun i j => raw2003 (permutation12 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2003 permutation12 permutation15
    _ = injectiveMoment H node820 := by rfl

def raw2004 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 1, -2, 1], ![1, 0, 2, -3], ![1, 0, 0, -1]]

def raw2004step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![0, 1, 0, -1], ![0, 1, 2, -3], ![1, 0, -2, 1]]

theorem canonical2004 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2004 = injectiveMoment H node819 := by
  calc
    injectiveMoment H raw2004 = injectiveMoment H raw2004step0 := by
      have heq : raw2004step0 = (fun i j => raw2004 (permutation14 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2004 permutation14 permutation15
    _ = injectiveMoment H node819 := by rfl

def raw2005 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 1, -2, 1], ![1, 0, 3, -4], ![1, 0, -1, 0]]

def raw2005step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![0, 1, -1, 0], ![0, 1, 3, -4], ![1, 0, -2, 1]]

theorem canonical2005 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2005 = injectiveMoment H node818 := by
  calc
    injectiveMoment H raw2005 = injectiveMoment H raw2005step0 := by
      have heq : raw2005step0 = (fun i j => raw2005 (permutation14 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2005 permutation14 permutation15
    _ = injectiveMoment H node818 := by rfl

def raw2006 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 1, -2, 1], ![1, 1, 1, -3], ![1, -1, 1, -1]]

def raw2006step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 1, -2, 1], ![1, -1, 1, -1], ![1, 1, 1, -3]]

theorem canonical2006 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2006 = injectiveMoment H node487 := by
  calc
    injectiveMoment H raw2006 = injectiveMoment H raw2006step0 := by
      have heq : raw2006step0 = (fun i j => raw2006 (permutation10 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2006 permutation10 permutation9
    _ = injectiveMoment H node487 := by rfl

def raw2007 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 1, -1, 0], ![0, 0, -1, 1], ![1, 0, -1, 0], ![1, 0, 3, -4]]

def raw2007step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![0, 0, -1, 1], ![0, 1, -1, 0], ![0, 1, 3, -4], ![1, 0, -1, 0]]

theorem canonical2007 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2007 = injectiveMoment H node2417 := by
  calc
    injectiveMoment H raw2007 = injectiveMoment H raw2007step0 := by
      have heq : raw2007step0 = (fun i j => raw2007 (permutation42 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2007 permutation42 permutation15
    _ = injectiveMoment H node2417 := by rfl

def raw2008 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 1, -1, 0], ![0, 0, 0, 0], ![1, 0, -1, 0], ![1, 0, 2, -3]]

def raw2008step0 : Matrix (Fin 4) (Fin 5) ℤ := ![![-2, 0, 0, 1, 1], ![-1, 1, 0, 0, 0], ![0, -1, 0, -1, 2], ![3, 0, 0, 0, -3]]

def raw2008step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![-1, 1, 0, 0], ![0, -1, -1, 2], ![3, 0, 0, -3]]

def raw2008step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -1, 0, 2], ![0, 0, 3, -3], ![0, 1, -2, 1], ![1, 0, -1, 0]]

theorem canonical2008 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2008 = injectiveMoment H node1063 := by
  calc
    injectiveMoment H raw2008 = injectiveMoment H raw2008step0 := by
      have heq : raw2008step0 = raw2008.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw2008).symm
    injectiveMoment H raw2008step0 = injectiveMoment H raw2008step1 := by
      have hz : ∀ i, raw2008step0 i (permutation80 0) = 0 := by decide +kernel
      have heq : raw2008step1 = (fun i j => raw2008step0 i (permutation80 j.succ)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_column (by decide) H raw2008step0 permutation80 hz
    injectiveMoment H raw2008step1 = injectiveMoment H raw2008step2 := by
      have heq : raw2008step2 = (fun i j => raw2008step1 (permutation25 i) (permutation17 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2008step1 permutation25 permutation17
    _ = injectiveMoment H node1063 := by rfl

def raw2009 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 1, -1, 0], ![0, 0, 0, 0], ![1, 0, 0, -1], ![1, 0, 1, -2]]

def raw2009step0 : Matrix (Fin 4) (Fin 5) ℤ := ![![-2, 0, 0, 1, 1], ![-1, 1, 0, 0, 0], ![0, -1, 0, 0, 1], ![3, 0, 0, -1, -2]]

def raw2009step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 1, 1], ![-1, 1, 0, 0], ![0, -1, 0, 1], ![3, 0, -1, -2]]

def raw2009step2 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, 0, -2, 3], ![0, -1, 1, 0], ![0, 1, 0, -1], ![1, 0, 1, -2]]

theorem canonical2009 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2009 = injectiveMoment H node1202 := by
  calc
    injectiveMoment H raw2009 = injectiveMoment H raw2009step0 := by
      have heq : raw2009step0 = raw2009.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw2009).symm
    injectiveMoment H raw2009step0 = injectiveMoment H raw2009step1 := by
      have hz : ∀ i, raw2009step0 i (permutation80 0) = 0 := by decide +kernel
      have heq : raw2009step1 = (fun i j => raw2009step0 i (permutation80 j.succ)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_column (by decide) H raw2009step0 permutation80 hz
    injectiveMoment H raw2009step1 = injectiveMoment H raw2009step2 := by
      have heq : raw2009step2 = (fun i j => raw2009step1 (permutation32 i) (permutation24 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2009step1 permutation32 permutation24
    _ = injectiveMoment H node1202 := by rfl

def raw2010 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 1, -1, 0], ![0, 0, 1, -1], ![1, 0, -1, 0], ![1, 0, 1, -2]]

def raw2010step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![0, 0, 1, -1], ![0, 1, -1, 0], ![0, 1, 1, -2], ![1, 0, -1, 0]]

theorem canonical2010 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2010 = injectiveMoment H node2425 := by
  calc
    injectiveMoment H raw2010 = injectiveMoment H raw2010step0 := by
      have heq : raw2010step0 = (fun i j => raw2010 (permutation42 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2010 permutation42 permutation15
    _ = injectiveMoment H node2425 := by rfl

def raw2011 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 1, -1, 0], ![0, 0, 2, -2], ![1, 0, -1, 0], ![1, 0, 0, -1]]

def raw2011step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![0, 0, 2, -2], ![0, 1, -1, 0], ![0, 1, 0, -1], ![1, 0, -1, 0]]

theorem canonical2011 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2011 = injectiveMoment H node2428 := by
  calc
    injectiveMoment H raw2011 = injectiveMoment H raw2011step0 := by
      have heq : raw2011step0 = (fun i j => raw2011 (permutation42 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2011 permutation42 permutation15
    _ = injectiveMoment H node2428 := by rfl

def raw2012 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 1, -1, 0], ![0, 0, 2, -2], ![2, 0, -1, -1]]

def raw2012step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![0, 0, 2, -2], ![0, 2, -1, -1], ![1, 0, -1, 0]]

theorem canonical2012 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2012 = injectiveMoment H node807 := by
  calc
    injectiveMoment H raw2012 = injectiveMoment H raw2012step0 := by
      have heq : raw2012step0 = (fun i j => raw2012 (permutation12 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2012 permutation12 permutation15
    _ = injectiveMoment H node807 := by rfl

def raw2013 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 1, -1, 0], ![0, 0, 3, -3], ![1, 0, -1, 0], ![1, 0, -1, 0]]

def raw2013step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![0, 0, 3, -3], ![0, 1, -1, 0], ![0, 1, -1, 0], ![1, 0, -1, 0]]

theorem canonical2013 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2013 = injectiveMoment H node2430 := by
  calc
    injectiveMoment H raw2013 = injectiveMoment H raw2013step0 := by
      have heq : raw2013step0 = (fun i j => raw2013 (permutation42 i) (permutation15 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2013 permutation42 permutation15
    _ = injectiveMoment H node2430 := by rfl

def raw2014 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 1, -1, 0], ![0, 1, -2, 1], ![1, -1, 0, 0], ![1, 0, 3, -4]]

def raw2014step0 : Matrix (Fin 5) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 1, -2, 1], ![0, 1, -1, 0], ![1, -1, 0, 0], ![1, 0, 3, -4]]

theorem canonical2014 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2014 = injectiveMoment H node1707 := by
  calc
    injectiveMoment H raw2014 = injectiveMoment H raw2014step0 := by
      have heq : raw2014step0 = (fun i j => raw2014 (permutation39 i) (permutation9 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2014 permutation39 permutation9
    _ = injectiveMoment H node1707 := by rfl

def raw2015 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, -1, 0, 3], ![0, 1, -1, 0], ![0, 1, -2, 1], ![2, -1, 3, -4]]

def raw2015step0 : Matrix (Fin 4) (Fin 4) ℤ := ![![-2, 0, 0, 2], ![-1, 1, 1, -1], ![0, -1, -2, 3], ![3, 0, 1, -4]]

def raw2015step1 : Matrix (Fin 4) (Fin 4) ℤ := ![![-1, -2, 0, 3], ![0, 0, -2, 2], ![0, 1, 3, -4], ![1, 1, -1, -1]]

theorem canonical2015 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw2015 = injectiveMoment H node792 := by
  calc
    injectiveMoment H raw2015 = injectiveMoment H raw2015step0 := by
      have heq : raw2015step0 = raw2015.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw2015).symm
    injectiveMoment H raw2015step0 = injectiveMoment H raw2015step1 := by
      have heq : raw2015step1 = (fun i j => raw2015step0 (permutation22 i) (permutation17 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw2015step0 permutation22 permutation17
    _ = injectiveMoment H node792 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
