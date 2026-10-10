import Mathlib
import OAI.Geometry.Borsuk.FiniteCases.Cases063
import OAI.Geometry.Borsuk.FiniteCases.Cases064
import OAI.Geometry.Borsuk.FiniteCases.Cases065
import OAI.Geometry.Borsuk.FiniteCases.Cases066
import OAI.Geometry.Borsuk.FiniteCases.Cases067
import OAI.Geometry.Borsuk.FiniteCases.Cases068
import OAI.Geometry.Borsuk.FiniteCases.Cases069
import OAI.Geometry.Borsuk.FiniteCases.Cases076

namespace OAI

open Set MeasureTheory
namespace BorsukNine.FiniteObstruction
attribute [local instance] Classical.propDecidable
variable {T Q : Family}

theorem c32212 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    Q {2, 4, 6, 7} → T {0, 3, 5} → T {0, 3, 9} → False := by
  classical
  intro a280 a17 a21
  have u0_2 : T {0, 1, 3} := by
    by_contra hv
    exact c31204 h h0 hv
  exact c24093 h a280 u0_2 a17 a21

theorem c32213 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    Q {2, 4, 6, 7} → T {0, 3, 8} → T {0, 3, 9} → False := by
  classical
  intro a280 a20 a21
  have u0_2 : T {0, 1, 3} := by
    by_contra hv
    exact c31204 h h0 hv
  exact c24095 h a280 u0_2 a20 a21

theorem c32215 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    T {1, 3, 5} → Q {2, 4, 6, 7} → T {1, 3, 9} → False := by
  classical
  intro a45 a280 a49
  have u0_2 : T {0, 1, 3} := by
    by_contra hv
    exact c31204 h h0 hv
  exact c24125 h a280 u0_2 a45 a49

theorem c32216 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    Q {2, 4, 6, 7} → T {1, 3, 8} → T {1, 3, 9} → False := by
  classical
  intro a280 a48 a49
  have u0_2 : T {0, 1, 3} := by
    by_contra hv
    exact c31204 h h0 hv
  exact c24127 h a280 u0_2 a48 a49

theorem c32225 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    Q {2, 4, 6, 8} → T {1, 3, 5} → T {1, 3, 9} → False := by
  classical
  intro a281 a45 a49
  have u0_2 : T {0, 1, 3} := by
    by_contra hv
    exact c31204 h h0 hv
  exact c24265 h a281 u0_2 a45 a49

theorem c32227 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    Q {2, 4, 6, 9} → T {5, 7, 8} → False := by
  classical
  intro a282 a114
  have u0_2 : T {0, 1, 3} := by
    by_contra hv
    exact c31204 h h0 hv
  exact c24343 h a282 u0_2 a114

theorem c32229 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    Q {2, 4, 6, 9} → T {0, 1, 8} → T {0, 1, 5} → False := by
  classical
  intro a282 a7 a4
  have u0_2 : T {0, 1, 3} := by
    by_contra hv
    exact c31204 h h0 hv
  exact c24365 h a282 u0_2 a4 a7

theorem c32235 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    Q {2, 4, 6, 9} → T {1, 3, 5} → T {1, 3, 8} → False := by
  classical
  intro a282 a45 a48
  have u0_2 : T {0, 1, 3} := by
    by_contra hv
    exact c31204 h h0 hv
  exact c24405 h a282 u0_2 a45 a48

theorem c32243 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    Q {2, 4, 7, 8} → T {0, 3, 6} → T {0, 3, 9} → False := by
  classical
  intro a283 a18 a21
  have u0_2 : T {0, 1, 3} := by
    by_contra hv
    exact c31204 h h0 hv
  exact c24515 h a283 u0_2 a18 a21

theorem c32247 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    Q {2, 4, 7, 9} → T {5, 6, 8} → False := by
  classical
  intro a284 a112
  have u0_2 : T {0, 1, 3} := by
    by_contra hv
    exact c31204 h h0 hv
  exact c24623 h a284 u0_2 a112

theorem c32248 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    T {0, 1, 5} → Q {2, 4, 7, 9} → T {0, 1, 6} → False := by
  classical
  intro a4 a284 a5
  have u0_2 : T {0, 1, 3} := by
    by_contra hv
    exact c31204 h h0 hv
  exact c24643 h a284 u0_2 a4 a5

theorem c32250 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    T {0, 1, 8} → Q {2, 4, 7, 9} → T {0, 1, 6} → False := by
  classical
  intro a7 a284 a5
  have u0_2 : T {0, 1, 3} := by
    by_contra hv
    exact c31204 h h0 hv
  exact c24647 h a284 u0_2 a5 a7

theorem c32252 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    Q {2, 4, 7, 9} → T {0, 3, 5} → T {0, 3, 8} → False := by
  classical
  intro a284 a17 a20
  have u0_2 : T {0, 1, 3} := by
    by_contra hv
    exact c31204 h h0 hv
  exact c24653 h a284 u0_2 a17 a20

theorem c32267 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    Q {2, 5, 6, 7} → T {4, 8, 9} → False := by
  classical
  intro a286 a110
  have u0_2 : T {0, 1, 3} := by
    by_contra hv
    exact c31204 h h0 hv
  exact c24903 h a286 u0_2 a110

theorem c32277 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    Q {2, 5, 6, 8} → T {4, 7, 9} → False := by
  classical
  intro a287 a109
  have u0_2 : T {0, 1, 3} := by
    by_contra hv
    exact c31204 h h0 hv
  exact c25043 h a287 u0_2 a109

theorem c32282 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    Q {2, 5, 6, 8} → T {0, 3, 4} → T {0, 3, 9} → False := by
  classical
  intro a287 a16 a21
  have u0_2 : T {0, 1, 3} := by
    by_contra hv
    exact c31204 h h0 hv
  exact c25073 h a287 u0_2 a16 a21

theorem c32283 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    Q {2, 5, 6, 8} → T {0, 3, 7} → T {0, 3, 9} → False := by
  classical
  intro a287 a19 a21
  have u0_2 : T {0, 1, 3} := by
    by_contra hv
    exact c31204 h h0 hv
  exact c25075 h a287 u0_2 a19 a21

theorem c32287 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    Q {2, 5, 6, 9} → T {4, 7, 8} → False := by
  classical
  intro a288 a108
  have u0_2 : T {0, 1, 3} := by
    by_contra hv
    exact c31204 h h0 hv
  exact c25183 h a288 u0_2 a108

theorem c32301 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    T {0, 3, 4} → T {0, 3, 6} → Q {2, 5, 7, 8} → False := by
  classical
  intro a16 a18 a289
  have u0_2 : T {0, 1, 3} := by
    by_contra hv
    exact c31204 h h0 hv
  exact c25351 h a289 u0_2 a16 a18

theorem c32303 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    T {0, 3, 6} → T {0, 3, 9} → Q {2, 5, 7, 8} → False := by
  classical
  intro a18 a21 a289
  have u0_2 : T {0, 1, 3} := by
    by_contra hv
    exact c31204 h h0 hv
  exact c25355 h a289 u0_2 a18 a21

theorem c32317 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    Q {2, 5, 8, 9} → T {4, 6, 7} → False := by
  classical
  intro a291 a105
  have u0_2 : T {0, 1, 3} := by
    by_contra hv
    exact c31204 h h0 hv
  exact c25603 h a291 u0_2 a105

theorem c32323 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    T {0, 3, 7} → T {0, 3, 6} → Q {2, 5, 8, 9} → False := by
  classical
  intro a19 a18 a291
  have u0_2 : T {0, 1, 3} := by
    by_contra hv
    exact c31204 h h0 hv
  exact c25635 h a291 u0_2 a18 a19

theorem c32324 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    T {1, 3, 6} → T {1, 3, 4} → Q {2, 5, 8, 9} → False := by
  classical
  intro a46 a44 a291
  have u0_2 : T {0, 1, 3} := by
    by_contra hv
    exact c31204 h h0 hv
  exact c25663 h a291 u0_2 a44 a46

theorem c32326 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    T {1, 3, 6} → T {1, 3, 7} → Q {2, 5, 8, 9} → False := by
  classical
  intro a46 a47 a291
  have u0_2 : T {0, 1, 3} := by
    by_contra hv
    exact c31204 h h0 hv
  exact c25667 h a291 u0_2 a46 a47

theorem c32337 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    Q {2, 6, 7, 9} → T {4, 5, 8} → False := by
  classical
  intro a293 a103
  have u0_2 : T {0, 1, 3} := by
    by_contra hv
    exact c31204 h h0 hv
  exact c25883 h a293 u0_2 a103

theorem c32347 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    Q {2, 6, 8, 9} → T {4, 5, 7} → False := by
  classical
  intro a294 a102
  have u0_2 : T {0, 1, 3} := by
    by_contra hv
    exact c31204 h h0 hv
  exact c26023 h a294 u0_2 a102

theorem c32367 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    Q {3, 4, 5, 6} → T {7, 8, 9} → False := by
  classical
  intro a296 a120
  have u0_1 : T {0, 1, 2} := by
    by_contra hv
    exact c31203 h h0 hv
  exact c26303 h a296 u0_1 a120

theorem c32374 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    T {1, 2, 7} → Q {3, 4, 5, 6} → T {1, 2, 8} → False := by
  classical
  intro a41 a296 a42
  have u0_1 : T {0, 1, 2} := by
    by_contra hv
    exact c31203 h h0 hv
  exact c26363 h a296 u0_1 a41 a42

theorem c32375 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    T {1, 2, 7} → Q {3, 4, 5, 6} → T {1, 2, 9} → False := by
  classical
  intro a41 a296 a43
  have u0_1 : T {0, 1, 2} := by
    by_contra hv
    exact c31203 h h0 hv
  exact c26365 h a296 u0_1 a41 a43

theorem c32382 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    Q {3, 4, 5, 7} → T {0, 2, 6} → T {0, 2, 9} → False := by
  classical
  intro a297 a12 a15
  have u0_1 : T {0, 1, 2} := by
    by_contra hv
    exact c31203 h h0 hv
  exact c26473 h a297 u0_1 a12 a15

theorem c32385 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    Q {3, 4, 5, 7} → T {1, 2, 9} → T {1, 2, 6} → False := by
  classical
  intro a297 a43 a40
  have u0_1 : T {0, 1, 2} := by
    by_contra hv
    exact c31203 h h0 hv
  exact c26505 h a297 u0_1 a40 a43

theorem c32387 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    Q {3, 4, 5, 8} → T {6, 7, 9} → False := by
  classical
  intro a298 a118
  have u0_1 : T {0, 1, 2} := by
    by_contra hv
    exact c31203 h h0 hv
  exact c26583 h a298 u0_1 a118

theorem c32395 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    Q {3, 4, 5, 8} → T {1, 2, 9} → T {1, 2, 6} → False := by
  classical
  intro a298 a43 a40
  have u0_1 : T {0, 1, 2} := by
    by_contra hv
    exact c31203 h h0 hv
  exact c26645 h a298 u0_1 a40 a43

theorem c32396 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    T {1, 2, 7} → Q {3, 4, 5, 8} → T {1, 2, 9} → False := by
  classical
  intro a41 a298 a43
  have u0_1 : T {0, 1, 2} := by
    by_contra hv
    exact c31203 h h0 hv
  exact c26647 h a298 u0_1 a41 a43

theorem c32397 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    Q {3, 4, 5, 9} → T {6, 7, 8} → False := by
  classical
  intro a299 a117
  have u0_1 : T {0, 1, 2} := by
    by_contra hv
    exact c31203 h h0 hv
  exact c26723 h a299 u0_1 a117

theorem c32398 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    Q {3, 4, 5, 9} → T {0, 1, 7} → T {0, 1, 6} → False := by
  classical
  intro a299 a6 a5
  have u0_1 : T {0, 1, 2} := by
    by_contra hv
    exact c31203 h h0 hv
  exact c26743 h a299 u0_1 a5 a6

theorem c32405 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    Q {3, 4, 5, 9} → T {1, 2, 6} → T {1, 2, 8} → False := by
  classical
  intro a299 a40 a42
  have u0_1 : T {0, 1, 2} := by
    by_contra hv
    exact c31203 h h0 hv
  exact c26785 h a299 u0_1 a40 a42

theorem c32406 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    Q {3, 4, 5, 9} → T {1, 2, 7} → T {1, 2, 8} → False := by
  classical
  intro a299 a41 a42
  have u0_1 : T {0, 1, 2} := by
    by_contra hv
    exact c31203 h h0 hv
  exact c26787 h a299 u0_1 a41 a42

theorem c32407 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    Q {3, 4, 6, 7} → T {5, 8, 9} → False := by
  classical
  intro a300 a116
  have u0_1 : T {0, 1, 2} := by
    by_contra hv
    exact c31203 h h0 hv
  exact c26863 h a300 u0_1 a116

theorem c32411 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    T {0, 2, 8} → T {0, 2, 5} → Q {3, 4, 6, 7} → False := by
  classical
  intro a14 a11 a300
  have u0_1 : T {0, 1, 2} := by
    by_contra hv
    exact c31203 h h0 hv
  exact c26891 h a300 u0_1 a11 a14

theorem c32412 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    Q {3, 4, 6, 7} → T {0, 2, 9} → T {0, 2, 5} → False := by
  classical
  intro a300 a15 a11
  have u0_1 : T {0, 1, 2} := by
    by_contra hv
    exact c31203 h h0 hv
  exact c26893 h a300 u0_1 a11 a15

theorem c32415 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    T {1, 2, 5} → Q {3, 4, 6, 7} → T {1, 2, 9} → False := by
  classical
  intro a39 a300 a43
  have u0_1 : T {0, 1, 2} := by
    by_contra hv
    exact c31203 h h0 hv
  exact c26925 h a300 u0_1 a39 a43

theorem c32416 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    T {1, 2, 8} → Q {3, 4, 6, 7} → T {1, 2, 9} → False := by
  classical
  intro a42 a300 a43
  have u0_1 : T {0, 1, 2} := by
    by_contra hv
    exact c31203 h h0 hv
  exact c26927 h a300 u0_1 a42 a43

theorem c32424 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    Q {3, 4, 6, 8} → T {1, 2, 5} → T {1, 2, 7} → False := by
  classical
  intro a301 a39 a41
  have u0_1 : T {0, 1, 2} := by
    by_contra hv
    exact c31203 h h0 hv
  exact c27063 h a301 u0_1 a39 a41

theorem c32425 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    Q {3, 4, 6, 8} → T {1, 2, 5} → T {1, 2, 9} → False := by
  classical
  intro a301 a39 a43
  have u0_1 : T {0, 1, 2} := by
    by_contra hv
    exact c31203 h h0 hv
  exact c27065 h a301 u0_1 a39 a43

theorem c32426 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    Q {3, 4, 6, 8} → T {1, 2, 7} → T {1, 2, 9} → False := by
  classical
  intro a301 a41 a43
  have u0_1 : T {0, 1, 2} := by
    by_contra hv
    exact c31203 h h0 hv
  exact c27067 h a301 u0_1 a41 a43

theorem c32427 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    Q {3, 4, 6, 9} → T {5, 7, 8} → False := by
  classical
  intro a302 a114
  have u0_1 : T {0, 1, 2} := by
    by_contra hv
    exact c31203 h h0 hv
  exact c27143 h a302 u0_1 a114

end BorsukNine.FiniteObstruction

end OAI
