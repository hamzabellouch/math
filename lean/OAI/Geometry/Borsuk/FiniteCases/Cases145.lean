import Mathlib
import OAI.Geometry.Borsuk.FiniteCases.Cases144

namespace OAI

open Set MeasureTheory
namespace BorsukNine.FiniteObstruction
attribute [local instance] Classical.propDecidable
variable {T Q : Family}

private theorem c32879 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    T {2, 3, 4} → False := by
  classical
  intro a65
  have u0_70 : T {2, 3, 9} := by
    by_contra hv
    exact c32873 h h0 hv
  have u1_196 : Q {0, 5, 6, 8} := by
    by_contra hv
    exact c32851 h h0 hv
  exact c31885 h h0 a65 u0_70 u1_196

private theorem c32880 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    T {1, 4, 7} → False := by
  classical
  intro a52
  have u0_70 : T {2, 3, 9} := by
    by_contra hv
    exact c32873 h h0 hv
  have u1_196 : Q {0, 5, 6, 8} := by
    by_contra hv
    exact c32851 h h0 hv
  exact c12317 h u1_196 a52 u0_70

private theorem c32888 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    Q {0, 2, 3, 7} → False := by
  classical
  intro a152
  have u0_68 : ¬ T {2, 3, 7} := by
    intro hv
    exact c32878 h h0 hv
  exact c1008 h a152 u0_68

private theorem c32897 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    Q {0, 2, 3, 4} → False := by
  classical
  intro a149
  have u0_65 : ¬ T {2, 3, 4} := by
    intro hv
    exact c32879 h h0 hv
  exact c963 h a149 u0_65

private theorem c32906 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    Q {0, 2, 3, 6} → False := by
  classical
  intro a151
  have u0_52 : ¬ T {1, 4, 7} := by
    intro hv
    exact c32880 h h0 hv
  have u1_116 : ¬ T {5, 8, 9} := by
    intro hv
    exact c32743 h h0 hv
  exact c6004 h a151 u0_52 u1_116

private theorem c32921 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    False := by
  classical
  have u0_149 : ¬ Q {0, 2, 3, 4} := by
    intro hv
    exact c32897 h h0 hv
  have u1_152 : ¬ Q {0, 2, 3, 7} := by
    intro hv
    exact c32888 h h0 hv
  have u2_153 : ¬ Q {0, 2, 3, 8} := by
    intro hv
    exact c32830 h h0 hv
  have u3_151 : ¬ Q {0, 2, 3, 6} := by
    intro hv
    exact c32906 h h0 hv
  have u4_154 : ¬ Q {0, 2, 3, 9} := by
    intro hv
    exact c32696 h h0 hv
  have u5_150 : ¬ Q {0, 2, 3, 5} := by
    intro hv
    exact c32831 h h0 hv
  exact c31534 h h0 u2_153 u5_150 u0_149 u4_154 u1_152 u3_151

theorem no_fixed_ten_system (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) : False :=
  c32921 h h0

theorem no_ten_system (h : TenSystem T Q) (hQ : ∃ S, Q S) : False := by
  obtain ⟨S, hS⟩ := hQ
  obtain ⟨e, he⟩ := Equiv.Perm.exists_map_finset_eq ( {0, 1, 2, 3} : Finset Labels) S (by rw [h.tetra_card S hS]; decide)
  exact no_fixed_ten_system (h.relabel e) (by simpa only [he] using hS)

end BorsukNine.FiniteObstruction

end OAI
