import OAI.Analysis.MutuallyUnbiased.MixedTargets.ReductionMergeData57
import OAI.Analysis.MutuallyUnbiased.MixedTargets.ReductionMergeSound56
import OAI.Analysis.MutuallyUnbiased.MixedTargets.ReductionSound57
import OAI.Analysis.MutuallyUnbiased.MixedTargets.ReductionSound58

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

theorem reducedMergeEval1824 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1824 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1824 (originalVector B) := by
  rw [reducedMerge1824Check, Integer.Sparse.eval_mergeBy, reducedTermEval1830 B hB hF, reducedTermEval1831 B hB hF]
  rw [originalMerge1824, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1825 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1825 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1825 (originalVector B) := by
  rw [reducedMerge1825Check, Integer.Sparse.eval_mergeBy, reducedTermEval1829 B hB hF, reducedMergeEval1824 B hB hF]
  rw [originalMerge1825, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1826 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1826 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1826 (originalVector B) := by
  rw [reducedMerge1826Check, Integer.Sparse.eval_mergeBy, reducedTermEval1832 B hB hF, reducedTermEval1833 B hB hF]
  rw [originalMerge1826, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1827 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1827 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1827 (originalVector B) := by
  rw [reducedMerge1827Check, Integer.Sparse.eval_mergeBy, reducedTermEval1834 B hB hF, reducedTermEval1835 B hB hF]
  rw [originalMerge1827, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1828 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1828 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1828 (originalVector B) := by
  rw [reducedMerge1828Check, Integer.Sparse.eval_mergeBy, reducedMergeEval1826 B hB hF, reducedMergeEval1827 B hB hF]
  rw [originalMerge1828, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1829 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1829 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1829 (originalVector B) := by
  rw [reducedMerge1829Check, Integer.Sparse.eval_mergeBy, reducedMergeEval1825 B hB hF, reducedMergeEval1828 B hB hF]
  rw [originalMerge1829, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1830 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1830 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1830 (originalVector B) := by
  rw [reducedMerge1830Check, Integer.Sparse.eval_mergeBy, reducedTermEval1836 B hB hF, reducedTermEval1837 B hB hF]
  rw [originalMerge1830, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1831 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1831 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1831 (originalVector B) := by
  rw [reducedMerge1831Check, Integer.Sparse.eval_mergeBy, reducedTermEval1838 B hB hF, reducedTermEval1839 B hB hF]
  rw [originalMerge1831, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1832 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1832 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1832 (originalVector B) := by
  rw [reducedMerge1832Check, Integer.Sparse.eval_mergeBy, reducedMergeEval1830 B hB hF, reducedMergeEval1831 B hB hF]
  rw [originalMerge1832, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1833 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1833 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1833 (originalVector B) := by
  rw [reducedMerge1833Check, Integer.Sparse.eval_mergeBy, reducedTermEval1840 B hB hF, reducedTermEval1841 B hB hF]
  rw [originalMerge1833, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1834 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1834 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1834 (originalVector B) := by
  rw [reducedMerge1834Check, Integer.Sparse.eval_mergeBy, reducedTermEval1842 B hB hF, reducedTermEval1843 B hB hF]
  rw [originalMerge1834, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1835 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1835 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1835 (originalVector B) := by
  rw [reducedMerge1835Check, Integer.Sparse.eval_mergeBy, reducedMergeEval1833 B hB hF, reducedMergeEval1834 B hB hF]
  rw [originalMerge1835, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1836 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1836 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1836 (originalVector B) := by
  rw [reducedMerge1836Check, Integer.Sparse.eval_mergeBy, reducedMergeEval1832 B hB hF, reducedMergeEval1835 B hB hF]
  rw [originalMerge1836, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1837 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1837 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1837 (originalVector B) := by
  rw [reducedMerge1837Check, Integer.Sparse.eval_mergeBy, reducedMergeEval1829 B hB hF, reducedMergeEval1836 B hB hF]
  rw [originalMerge1837, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1838 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1838 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1838 (originalVector B) := by
  rw [reducedMerge1838Check, Integer.Sparse.eval_mergeBy, reducedTermEval1845 B hB hF, reducedTermEval1846 B hB hF]
  rw [originalMerge1838, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1839 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1839 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1839 (originalVector B) := by
  rw [reducedMerge1839Check, Integer.Sparse.eval_mergeBy, reducedTermEval1844 B hB hF, reducedMergeEval1838 B hB hF]
  rw [originalMerge1839, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1840 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1840 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1840 (originalVector B) := by
  rw [reducedMerge1840Check, Integer.Sparse.eval_mergeBy, reducedTermEval1847 B hB hF, reducedTermEval1848 B hB hF]
  rw [originalMerge1840, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1841 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1841 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1841 (originalVector B) := by
  rw [reducedMerge1841Check, Integer.Sparse.eval_mergeBy, reducedTermEval1849 B hB hF, reducedTermEval1850 B hB hF]
  rw [originalMerge1841, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1842 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1842 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1842 (originalVector B) := by
  rw [reducedMerge1842Check, Integer.Sparse.eval_mergeBy, reducedMergeEval1840 B hB hF, reducedMergeEval1841 B hB hF]
  rw [originalMerge1842, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1843 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1843 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1843 (originalVector B) := by
  rw [reducedMerge1843Check, Integer.Sparse.eval_mergeBy, reducedMergeEval1839 B hB hF, reducedMergeEval1842 B hB hF]
  rw [originalMerge1843, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1844 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1844 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1844 (originalVector B) := by
  rw [reducedMerge1844Check, Integer.Sparse.eval_mergeBy, reducedTermEval1851 B hB hF, reducedTermEval1852 B hB hF]
  rw [originalMerge1844, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1845 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1845 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1845 (originalVector B) := by
  rw [reducedMerge1845Check, Integer.Sparse.eval_mergeBy, reducedTermEval1853 B hB hF, reducedTermEval1854 B hB hF]
  rw [originalMerge1845, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1846 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1846 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1846 (originalVector B) := by
  rw [reducedMerge1846Check, Integer.Sparse.eval_mergeBy, reducedMergeEval1844 B hB hF, reducedMergeEval1845 B hB hF]
  rw [originalMerge1846, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1847 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1847 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1847 (originalVector B) := by
  rw [reducedMerge1847Check, Integer.Sparse.eval_mergeBy, reducedTermEval1855 B hB hF, reducedTermEval1856 B hB hF]
  rw [originalMerge1847, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1848 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1848 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1848 (originalVector B) := by
  rw [reducedMerge1848Check, Integer.Sparse.eval_mergeBy, reducedTermEval1857 B hB hF, reducedTermEval1858 B hB hF]
  rw [originalMerge1848, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1849 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1849 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1849 (originalVector B) := by
  rw [reducedMerge1849Check, Integer.Sparse.eval_mergeBy, reducedMergeEval1847 B hB hF, reducedMergeEval1848 B hB hF]
  rw [originalMerge1849, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1850 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1850 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1850 (originalVector B) := by
  rw [reducedMerge1850Check, Integer.Sparse.eval_mergeBy, reducedMergeEval1846 B hB hF, reducedMergeEval1849 B hB hF]
  rw [originalMerge1850, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1851 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1851 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1851 (originalVector B) := by
  rw [reducedMerge1851Check, Integer.Sparse.eval_mergeBy, reducedMergeEval1843 B hB hF, reducedMergeEval1850 B hB hF]
  rw [originalMerge1851, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1852 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1852 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1852 (originalVector B) := by
  rw [reducedMerge1852Check, Integer.Sparse.eval_mergeBy, reducedMergeEval1837 B hB hF, reducedMergeEval1851 B hB hF]
  rw [originalMerge1852, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1853 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1853 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1853 (originalVector B) := by
  rw [reducedMerge1853Check, Integer.Sparse.eval_mergeBy, reducedMergeEval1823 B hB hF, reducedMergeEval1852 B hB hF]
  rw [originalMerge1853, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1854 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1854 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1854 (originalVector B) := by
  rw [reducedMerge1854Check, Integer.Sparse.eval_mergeBy, reducedTermEval1860 B hB hF, reducedTermEval1861 B hB hF]
  rw [originalMerge1854, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1855 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1855 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1855 (originalVector B) := by
  rw [reducedMerge1855Check, Integer.Sparse.eval_mergeBy, reducedTermEval1859 B hB hF, reducedMergeEval1854 B hB hF]
  rw [originalMerge1855, Integer.Sparse.eval_append]
  ring

end MUB6.Certificate.MixedTargetSemantics

end OAI
