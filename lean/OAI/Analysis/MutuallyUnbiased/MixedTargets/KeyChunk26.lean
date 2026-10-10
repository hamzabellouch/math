import OAI.Analysis.MutuallyUnbiased.MixedTargets.KeySound26
import OAI.Analysis.MutuallyUnbiased.MixedTargets.KeyTable

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

theorem keyMomentRowsAt832 : keyMomentRows (832 : Fin 2886) =
    keyMomentRow832 := by decide +kernel

theorem keyMomentRowsAt833 : keyMomentRows (833 : Fin 2886) =
    keyMomentRow833 := by decide +kernel

theorem keyMomentRowsAt834 : keyMomentRows (834 : Fin 2886) =
    keyMomentRow834 := by decide +kernel

theorem keyMomentRowsAt835 : keyMomentRows (835 : Fin 2886) =
    keyMomentRow835 := by decide +kernel

theorem keyMomentRowsAt836 : keyMomentRows (836 : Fin 2886) =
    keyMomentRow836 := by decide +kernel

theorem keyMomentRowsAt837 : keyMomentRows (837 : Fin 2886) =
    keyMomentRow837 := by decide +kernel

theorem keyMomentRowsAt838 : keyMomentRows (838 : Fin 2886) =
    keyMomentRow838 := by decide +kernel

theorem keyMomentRowsAt839 : keyMomentRows (839 : Fin 2886) =
    keyMomentRow839 := by decide +kernel

theorem keyMomentRowsAt840 : keyMomentRows (840 : Fin 2886) =
    keyMomentRow840 := by decide +kernel

theorem keyMomentRowsAt841 : keyMomentRows (841 : Fin 2886) =
    keyMomentRow841 := by decide +kernel

theorem keyMomentRowsAt842 : keyMomentRows (842 : Fin 2886) =
    keyMomentRow842 := by decide +kernel

theorem keyMomentRowsAt843 : keyMomentRows (843 : Fin 2886) =
    keyMomentRow843 := by decide +kernel

theorem keyMomentRowsAt844 : keyMomentRows (844 : Fin 2886) =
    keyMomentRow844 := by decide +kernel

theorem keyMomentRowsAt845 : keyMomentRows (845 : Fin 2886) =
    keyMomentRow845 := by decide +kernel

theorem keyMomentRowsAt846 : keyMomentRows (846 : Fin 2886) =
    keyMomentRow846 := by decide +kernel

theorem keyMomentRowsAt847 : keyMomentRows (847 : Fin 2886) =
    keyMomentRow847 := by decide +kernel

theorem keyMomentRowsAt848 : keyMomentRows (848 : Fin 2886) =
    keyMomentRow848 := by decide +kernel

theorem keyMomentRowsAt849 : keyMomentRows (849 : Fin 2886) =
    keyMomentRow849 := by decide +kernel

theorem keyMomentRowsAt850 : keyMomentRows (850 : Fin 2886) =
    keyMomentRow850 := by decide +kernel

theorem keyMomentRowsAt851 : keyMomentRows (851 : Fin 2886) =
    keyMomentRow851 := by decide +kernel

theorem keyMomentRowsAt852 : keyMomentRows (852 : Fin 2886) =
    keyMomentRow852 := by decide +kernel

theorem keyMomentRowsAt853 : keyMomentRows (853 : Fin 2886) =
    keyMomentRow853 := by decide +kernel

theorem keyMomentRowsAt854 : keyMomentRows (854 : Fin 2886) =
    keyMomentRow854 := by decide +kernel

theorem keyMomentRowsAt855 : keyMomentRows (855 : Fin 2886) =
    keyMomentRow855 := by decide +kernel

theorem keyMomentRowsAt856 : keyMomentRows (856 : Fin 2886) =
    keyMomentRow856 := by decide +kernel

theorem keyMomentRowsAt857 : keyMomentRows (857 : Fin 2886) =
    keyMomentRow857 := by decide +kernel

theorem keyMomentRowsAt858 : keyMomentRows (858 : Fin 2886) =
    keyMomentRow858 := by decide +kernel

theorem keyMomentRowsAt859 : keyMomentRows (859 : Fin 2886) =
    keyMomentRow859 := by decide +kernel

theorem keyMomentRowsAt860 : keyMomentRows (860 : Fin 2886) =
    keyMomentRow860 := by decide +kernel

theorem keyMomentRowsAt861 : keyMomentRows (861 : Fin 2886) =
    keyMomentRow861 := by decide +kernel

theorem keyMomentRowsAt862 : keyMomentRows (862 : Fin 2886) =
    keyMomentRow862 := by decide +kernel

theorem keyMomentRowsAt863 : keyMomentRows (863 : Fin 2886) =
    keyMomentRow863 := by decide +kernel

theorem keyMomentChunkSound26 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (k : Fin 2886) (hk : k.val / 32 = 26) :
    5 * GramNormalization.eval B (GramAssembly.key k) =
      Integer.Sparse.eval (keyMomentRows k) (originalVector B) := by
  have heq : k.val = 832 ∨ k.val = 833 ∨ k.val = 834 ∨ k.val = 835 ∨ k.val = 836 ∨ k.val = 837 ∨ k.val = 838 ∨ k.val = 839 ∨ k.val = 840 ∨ k.val = 841 ∨ k.val = 842 ∨ k.val = 843 ∨ k.val = 844 ∨ k.val = 845 ∨ k.val = 846 ∨ k.val = 847 ∨ k.val = 848 ∨ k.val = 849 ∨ k.val = 850 ∨ k.val = 851 ∨ k.val = 852 ∨ k.val = 853 ∨ k.val = 854 ∨ k.val = 855 ∨ k.val = 856 ∨ k.val = 857 ∨ k.val = 858 ∨ k.val = 859 ∨ k.val = 860 ∨ k.val = 861 ∨ k.val = 862 ∨ k.val = 863 := by omega
  rcases heq with h832 | h833 | h834 | h835 | h836 | h837 | h838 | h839 | h840 | h841 | h842 | h843 | h844 | h845 | h846 | h847 | h848 | h849 | h850 | h851 | h852 | h853 | h854 | h855 | h856 | h857 | h858 | h859 | h860 | h861 | h862 | h863
  · have he : k = (832 : Fin 2886) := Fin.ext h832
    subst k
    rw [keyMomentRowsAt832]
    exact keyMoment832 B hB
  · have he : k = (833 : Fin 2886) := Fin.ext h833
    subst k
    rw [keyMomentRowsAt833]
    exact keyMoment833 B hB
  · have he : k = (834 : Fin 2886) := Fin.ext h834
    subst k
    rw [keyMomentRowsAt834]
    exact keyMoment834 B hB
  · have he : k = (835 : Fin 2886) := Fin.ext h835
    subst k
    rw [keyMomentRowsAt835]
    exact keyMoment835 B hB
  · have he : k = (836 : Fin 2886) := Fin.ext h836
    subst k
    rw [keyMomentRowsAt836]
    exact keyMoment836 B hB
  · have he : k = (837 : Fin 2886) := Fin.ext h837
    subst k
    rw [keyMomentRowsAt837]
    exact keyMoment837 B hB
  · have he : k = (838 : Fin 2886) := Fin.ext h838
    subst k
    rw [keyMomentRowsAt838]
    exact keyMoment838 B hB
  · have he : k = (839 : Fin 2886) := Fin.ext h839
    subst k
    rw [keyMomentRowsAt839]
    exact keyMoment839 B hB
  · have he : k = (840 : Fin 2886) := Fin.ext h840
    subst k
    rw [keyMomentRowsAt840]
    exact keyMoment840 B hB
  · have he : k = (841 : Fin 2886) := Fin.ext h841
    subst k
    rw [keyMomentRowsAt841]
    exact keyMoment841 B hB
  · have he : k = (842 : Fin 2886) := Fin.ext h842
    subst k
    rw [keyMomentRowsAt842]
    exact keyMoment842 B hB
  · have he : k = (843 : Fin 2886) := Fin.ext h843
    subst k
    rw [keyMomentRowsAt843]
    exact keyMoment843 B hB
  · have he : k = (844 : Fin 2886) := Fin.ext h844
    subst k
    rw [keyMomentRowsAt844]
    exact keyMoment844 B hB
  · have he : k = (845 : Fin 2886) := Fin.ext h845
    subst k
    rw [keyMomentRowsAt845]
    exact keyMoment845 B hB
  · have he : k = (846 : Fin 2886) := Fin.ext h846
    subst k
    rw [keyMomentRowsAt846]
    exact keyMoment846 B hB
  · have he : k = (847 : Fin 2886) := Fin.ext h847
    subst k
    rw [keyMomentRowsAt847]
    exact keyMoment847 B hB
  · have he : k = (848 : Fin 2886) := Fin.ext h848
    subst k
    rw [keyMomentRowsAt848]
    exact keyMoment848 B hB
  · have he : k = (849 : Fin 2886) := Fin.ext h849
    subst k
    rw [keyMomentRowsAt849]
    exact keyMoment849 B hB
  · have he : k = (850 : Fin 2886) := Fin.ext h850
    subst k
    rw [keyMomentRowsAt850]
    exact keyMoment850 B hB
  · have he : k = (851 : Fin 2886) := Fin.ext h851
    subst k
    rw [keyMomentRowsAt851]
    exact keyMoment851 B hB
  · have he : k = (852 : Fin 2886) := Fin.ext h852
    subst k
    rw [keyMomentRowsAt852]
    exact keyMoment852 B hB
  · have he : k = (853 : Fin 2886) := Fin.ext h853
    subst k
    rw [keyMomentRowsAt853]
    exact keyMoment853 B hB
  · have he : k = (854 : Fin 2886) := Fin.ext h854
    subst k
    rw [keyMomentRowsAt854]
    exact keyMoment854 B hB
  · have he : k = (855 : Fin 2886) := Fin.ext h855
    subst k
    rw [keyMomentRowsAt855]
    exact keyMoment855 B hB
  · have he : k = (856 : Fin 2886) := Fin.ext h856
    subst k
    rw [keyMomentRowsAt856]
    exact keyMoment856 B hB
  · have he : k = (857 : Fin 2886) := Fin.ext h857
    subst k
    rw [keyMomentRowsAt857]
    exact keyMoment857 B hB
  · have he : k = (858 : Fin 2886) := Fin.ext h858
    subst k
    rw [keyMomentRowsAt858]
    exact keyMoment858 B hB
  · have he : k = (859 : Fin 2886) := Fin.ext h859
    subst k
    rw [keyMomentRowsAt859]
    exact keyMoment859 B hB
  · have he : k = (860 : Fin 2886) := Fin.ext h860
    subst k
    rw [keyMomentRowsAt860]
    exact keyMoment860 B hB
  · have he : k = (861 : Fin 2886) := Fin.ext h861
    subst k
    rw [keyMomentRowsAt861]
    exact keyMoment861 B hB
  · have he : k = (862 : Fin 2886) := Fin.ext h862
    subst k
    rw [keyMomentRowsAt862]
    exact keyMoment862 B hB
  · have he : k = (863 : Fin 2886) := Fin.ext h863
    subst k
    rw [keyMomentRowsAt863]
    exact keyMoment863 B hB

end MUB6.Certificate.MixedTargetSemantics

end OAI
