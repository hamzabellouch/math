import Mathlib
import OAI.Geometry.Borsuk.FiniteCases.Cases042
import OAI.Geometry.Borsuk.FiniteCases.Cases043
import OAI.Geometry.Borsuk.FiniteCases.Cases044
import OAI.Geometry.Borsuk.FiniteCases.Cases053
import OAI.Geometry.Borsuk.FiniteCases.Cases054
import OAI.Geometry.Borsuk.FiniteCases.Cases055
import OAI.Geometry.Borsuk.FiniteCases.Cases056
import OAI.Geometry.Borsuk.FiniteCases.Cases057
import OAI.Geometry.Borsuk.FiniteCases.Cases058
import OAI.Geometry.Borsuk.FiniteCases.Cases059
import OAI.Geometry.Borsuk.FiniteCases.Cases062
import OAI.Geometry.Borsuk.FiniteCases.Cases063
import OAI.Geometry.Borsuk.FiniteCases.Cases076

namespace OAI

open Set MeasureTheory
namespace BorsukNine.FiniteObstruction
attribute [local instance] Classical.propDecidable
variable {T Q : Family}

theorem c31899 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    Q {0, 5, 7, 8} → T {1, 2, 4} → T {1, 2, 9} → False := by
  classical
  intro a198 a38 a43
  have u0_37 : T {1, 2, 3} := by
    by_contra hv
    exact c31206 h h0 hv
  exact c12605 h a198 u0_37 a38 a43

theorem c31900 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    Q {0, 5, 7, 8} → T {1, 2, 6} → T {1, 2, 9} → False := by
  classical
  intro a198 a40 a43
  have u0_37 : T {1, 2, 3} := by
    by_contra hv
    exact c31206 h h0 hv
  exact c12607 h a198 u0_37 a40 a43

theorem c31905 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    Q {0, 5, 7, 8} → T {2, 3, 4} → T {2, 3, 9} → False := by
  classical
  intro a198 a65 a70
  have u0_37 : T {1, 2, 3} := by
    by_contra hv
    exact c31206 h h0 hv
  exact c12645 h a198 u0_37 a65 a70

theorem c31906 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    Q {0, 5, 7, 8} → T {2, 3, 6} → T {2, 3, 9} → False := by
  classical
  intro a198 a67 a70
  have u0_37 : T {1, 2, 3} := by
    by_contra hv
    exact c31206 h h0 hv
  exact c12647 h a198 u0_37 a67 a70

theorem c31917 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    Q {0, 5, 8, 9} → T {4, 6, 7} → False := by
  classical
  intro a200 a105
  have u0_37 : T {1, 2, 3} := by
    by_contra hv
    exact c31206 h h0 hv
  exact c12863 h a200 u0_37 a105

theorem c31918 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    Q {0, 5, 8, 9} → T {1, 2, 6} → T {1, 2, 4} → False := by
  classical
  intro a200 a40 a38
  have u0_37 : T {1, 2, 3} := by
    by_contra hv
    exact c31206 h h0 hv
  exact c12883 h a200 u0_37 a38 a40

theorem c31919 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    Q {0, 5, 8, 9} → T {1, 2, 7} → T {1, 2, 4} → False := by
  classical
  intro a200 a41 a38
  have u0_37 : T {1, 2, 3} := by
    by_contra hv
    exact c31206 h h0 hv
  exact c12885 h a200 u0_37 a38 a41

theorem c31920 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    Q {0, 5, 8, 9} → T {1, 2, 6} → T {1, 2, 7} → False := by
  classical
  intro a200 a40 a41
  have u0_37 : T {1, 2, 3} := by
    by_contra hv
    exact c31206 h h0 hv
  exact c12887 h a200 u0_37 a40 a41

theorem c31923 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    Q {0, 5, 8, 9} → T {1, 3, 6} → T {1, 3, 7} → False := by
  classical
  intro a200 a46 a47
  have u0_37 : T {1, 2, 3} := by
    by_contra hv
    exact c31206 h h0 hv
  exact c12895 h a200 u0_37 a46 a47

theorem c31926 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    Q {0, 5, 8, 9} → T {2, 3, 6} → T {2, 3, 7} → False := by
  classical
  intro a200 a67 a68
  have u0_37 : T {1, 2, 3} := by
    by_contra hv
    exact c31206 h h0 hv
  exact c12927 h a200 u0_37 a67 a68

theorem c31929 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    Q {0, 6, 7, 8} → T {1, 2, 4} → T {1, 2, 9} → False := by
  classical
  intro a201 a38 a43
  have u0_37 : T {1, 2, 3} := by
    by_contra hv
    exact c31206 h h0 hv
  exact c13025 h a201 u0_37 a38 a43

theorem c31930 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    Q {0, 6, 7, 8} → T {1, 2, 5} → T {1, 2, 9} → False := by
  classical
  intro a201 a39 a43
  have u0_37 : T {1, 2, 3} := by
    by_contra hv
    exact c31206 h h0 hv
  exact c13027 h a201 u0_37 a39 a43

theorem c31947 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    Q {0, 6, 8, 9} → T {4, 5, 7} → False := by
  classical
  intro a203 a102
  have u0_37 : T {1, 2, 3} := by
    by_contra hv
    exact c31206 h h0 hv
  exact c13283 h a203 u0_37 a102

theorem c31957 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    Q {0, 7, 8, 9} → T {4, 5, 6} → False := by
  classical
  intro a204 a101
  have u0_37 : T {1, 2, 3} := by
    by_contra hv
    exact c31206 h h0 hv
  exact c13423 h a204 u0_37 a101

theorem c31967 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    Q {1, 4, 5, 6} → T {7, 8, 9} → False := by
  classical
  intro a241 a120
  have u0_9 : T {0, 2, 3} := by
    by_contra hv
    exact c31205 h h0 hv
  exact c18603 h a241 u0_9 a120

theorem c31976 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    Q {1, 4, 5, 6} → T {2, 3, 8} → T {2, 3, 9} → False := by
  classical
  intro a241 a69 a70
  have u0_9 : T {0, 2, 3} := by
    by_contra hv
    exact c31205 h h0 hv
  exact c18667 h a241 u0_9 a69 a70

theorem c31993 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    T {0, 3, 7} → T {0, 3, 9} → Q {1, 4, 5, 8} → False := by
  classical
  intro a19 a21 a243
  have u0_9 : T {0, 2, 3} := by
    by_contra hv
    exact c31205 h h0 hv
  exact c18915 h a243 u0_9 a19 a21

theorem c32011 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    T {0, 3, 8} → T {0, 3, 5} → Q {1, 4, 6, 7} → False := by
  classical
  intro a20 a17 a245
  have u0_9 : T {0, 2, 3} := by
    by_contra hv
    exact c31205 h h0 hv
  exact c19191 h a245 u0_9 a17 a20

theorem c32015 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    T {2, 3, 5} → Q {1, 4, 6, 7} → T {2, 3, 9} → False := by
  classical
  intro a66 a245 a70
  have u0_9 : T {0, 2, 3} := by
    by_contra hv
    exact c31205 h h0 hv
  exact c19225 h a245 u0_9 a66 a70

theorem c32016 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    T {2, 3, 8} → Q {1, 4, 6, 7} → T {2, 3, 9} → False := by
  classical
  intro a69 a245 a70
  have u0_9 : T {0, 2, 3} := by
    by_contra hv
    exact c31205 h h0 hv
  exact c19227 h a245 u0_9 a69 a70

theorem c32025 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    Q {1, 4, 6, 8} → T {2, 3, 5} → T {2, 3, 9} → False := by
  classical
  intro a246 a66 a70
  have u0_9 : T {0, 2, 3} := by
    by_contra hv
    exact c31205 h h0 hv
  exact c19365 h a246 u0_9 a66 a70

theorem c32033 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    T {0, 3, 8} → T {0, 3, 7} → Q {1, 4, 6, 9} → False := by
  classical
  intro a20 a19 a247
  have u0_9 : T {0, 2, 3} := by
    by_contra hv
    exact c31205 h h0 hv
  exact c19475 h a247 u0_9 a19 a20

theorem c32047 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    Q {1, 4, 7, 9} → T {5, 6, 8} → False := by
  classical
  intro a249 a112
  have u0_9 : T {0, 2, 3} := by
    by_contra hv
    exact c31205 h h0 hv
  exact c19723 h a249 u0_9 a112

theorem c32052 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    T {0, 3, 5} → T {0, 3, 8} → Q {1, 4, 7, 9} → False := by
  classical
  intro a17 a20 a249
  have u0_9 : T {0, 2, 3} := by
    by_contra hv
    exact c31205 h h0 hv
  exact c19753 h a249 u0_9 a17 a20

theorem c32085 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    Q {1, 5, 6, 8} → T {2, 3, 4} → T {2, 3, 9} → False := by
  classical
  intro a252 a65 a70
  have u0_9 : T {0, 2, 3} := by
    by_contra hv
    exact c31205 h h0 hv
  exact c20205 h a252 u0_9 a65 a70

theorem c32086 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    Q {1, 5, 6, 8} → T {2, 3, 9} → T {2, 3, 7} → False := by
  classical
  intro a252 a70 a68
  have u0_9 : T {0, 2, 3} := by
    by_contra hv
    exact c31205 h h0 hv
  exact c20207 h a252 u0_9 a68 a70

theorem c32087 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    Q {1, 5, 6, 9} → T {4, 7, 8} → False := by
  classical
  intro a253 a108
  have u0_9 : T {0, 2, 3} := by
    by_contra hv
    exact c31205 h h0 hv
  exact c20283 h a253 u0_9 a108

theorem c32101 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    T {0, 3, 4} → Q {1, 5, 7, 8} → T {0, 3, 6} → False := by
  classical
  intro a16 a254 a18
  have u0_9 : T {0, 2, 3} := by
    by_contra hv
    exact c31205 h h0 hv
  exact c20451 h a254 u0_9 a16 a18

theorem c32117 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    Q {1, 5, 8, 9} → T {4, 6, 7} → False := by
  classical
  intro a256 a105
  have u0_9 : T {0, 2, 3} := by
    by_contra hv
    exact c31205 h h0 hv
  exact c20703 h a256 u0_9 a105

theorem c32121 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    T {0, 3, 4} → T {0, 3, 6} → Q {1, 5, 8, 9} → False := by
  classical
  intro a16 a18 a256
  have u0_9 : T {0, 2, 3} := by
    by_contra hv
    exact c31205 h h0 hv
  exact c20731 h a256 u0_9 a16 a18

theorem c32123 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    T {0, 3, 7} → T {0, 3, 6} → Q {1, 5, 8, 9} → False := by
  classical
  intro a19 a18 a256
  have u0_9 : T {0, 2, 3} := by
    by_contra hv
    exact c31205 h h0 hv
  exact c20735 h a256 u0_9 a18 a19

theorem c32126 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    T {2, 3, 6} → T {2, 3, 7} → Q {1, 5, 8, 9} → False := by
  classical
  intro a67 a68 a256
  have u0_9 : T {0, 2, 3} := by
    by_contra hv
    exact c31205 h h0 hv
  exact c20767 h a256 u0_9 a67 a68

theorem c32137 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    Q {1, 6, 7, 9} → T {4, 5, 8} → False := by
  classical
  intro a258 a103
  have u0_9 : T {0, 2, 3} := by
    by_contra hv
    exact c31205 h h0 hv
  exact c20983 h a258 u0_9 a103

theorem c32147 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    Q {1, 6, 8, 9} → T {4, 5, 7} → False := by
  classical
  intro a259 a102
  have u0_9 : T {0, 2, 3} := by
    by_contra hv
    exact c31205 h h0 hv
  exact c21123 h a259 u0_9 a102

theorem c32148 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    Q {1, 6, 8, 9} → T {0, 2, 5} → T {0, 2, 4} → False := by
  classical
  intro a259 a11 a10
  have u0_9 : T {0, 2, 3} := by
    by_contra hv
    exact c31205 h h0 hv
  exact c21143 h a259 u0_9 a10 a11

theorem c32157 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    Q {1, 7, 8, 9} → T {4, 5, 6} → False := by
  classical
  intro a260 a101
  have u0_9 : T {0, 2, 3} := by
    by_contra hv
    exact c31205 h h0 hv
  exact c21263 h a260 u0_9 a101

theorem c32166 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    T {2, 3, 5} → Q {1, 7, 8, 9} → T {2, 3, 6} → False := by
  classical
  intro a66 a260 a67
  have u0_9 : T {0, 2, 3} := by
    by_contra hv
    exact c31205 h h0 hv
  exact c21327 h a260 u0_9 a66 a67

theorem c32167 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    Q {2, 4, 5, 6} → T {7, 8, 9} → False := by
  classical
  intro a276 a120
  have u0_2 : T {0, 1, 3} := by
    by_contra hv
    exact c31204 h h0 hv
  exact c23503 h a276 u0_2 a120

theorem c32176 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    Q {2, 4, 5, 6} → T {1, 3, 8} → T {1, 3, 9} → False := by
  classical
  intro a276 a48 a49
  have u0_2 : T {0, 1, 3} := by
    by_contra hv
    exact c31204 h h0 hv
  exact c23567 h a276 u0_2 a48 a49

theorem c32182 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    Q {2, 4, 5, 7} → T {0, 3, 6} → T {0, 3, 9} → False := by
  classical
  intro a277 a18 a21
  have u0_2 : T {0, 1, 3} := by
    by_contra hv
    exact c31204 h h0 hv
  exact c23673 h a277 u0_2 a18 a21

theorem c32192 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    Q {2, 4, 5, 8} → T {0, 3, 6} → T {0, 3, 9} → False := by
  classical
  intro a278 a18 a21
  have u0_2 : T {0, 1, 3} := by
    by_contra hv
    exact c31204 h h0 hv
  exact c23813 h a278 u0_2 a18 a21

theorem c32193 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    Q {2, 4, 5, 8} → T {0, 3, 7} → T {0, 3, 9} → False := by
  classical
  intro a278 a19 a21
  have u0_2 : T {0, 1, 3} := by
    by_contra hv
    exact c31204 h h0 hv
  exact c23815 h a278 u0_2 a19 a21

theorem c32197 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    Q {2, 4, 5, 9} → T {6, 7, 8} → False := by
  classical
  intro a279 a117
  have u0_2 : T {0, 1, 3} := by
    by_contra hv
    exact c31204 h h0 hv
  exact c23923 h a279 u0_2 a117

theorem c32207 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    Q {2, 4, 6, 7} → T {5, 8, 9} → False := by
  classical
  intro a280 a116
  have u0_2 : T {0, 1, 3} := by
    by_contra hv
    exact c31204 h h0 hv
  exact c24063 h a280 u0_2 a116

theorem c32209 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    Q {2, 4, 6, 7} → T {0, 1, 5} → T {0, 1, 9} → False := by
  classical
  intro a280 a4 a8
  have u0_2 : T {0, 1, 3} := by
    by_contra hv
    exact c31204 h h0 hv
  exact c24085 h a280 u0_2 a4 a8

theorem c32210 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    Q {2, 4, 6, 7} → T {0, 1, 8} → T {0, 1, 9} → False := by
  classical
  intro a280 a7 a8
  have u0_2 : T {0, 1, 3} := by
    by_contra hv
    exact c31204 h h0 hv
  exact c24087 h a280 u0_2 a7 a8

theorem c32211 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    Q {2, 4, 6, 7} → T {0, 3, 8} → T {0, 3, 5} → False := by
  classical
  intro a280 a20 a17
  have u0_2 : T {0, 1, 3} := by
    by_contra hv
    exact c31204 h h0 hv
  exact c24091 h a280 u0_2 a17 a20

end BorsukNine.FiniteObstruction

end OAI
