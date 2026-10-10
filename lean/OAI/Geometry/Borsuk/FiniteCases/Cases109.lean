import Mathlib
import OAI.Geometry.Borsuk.FiniteCases.Cases102
import OAI.Geometry.Borsuk.FiniteCases.Cases103
import OAI.Geometry.Borsuk.FiniteCases.Cases104
import OAI.Geometry.Borsuk.FiniteCases.Cases105
import OAI.Geometry.Borsuk.FiniteCases.Cases106
import OAI.Geometry.Borsuk.FiniteCases.Cases107
import OAI.Geometry.Borsuk.FiniteCases.Cases108

namespace OAI

open Set MeasureTheory
namespace BorsukNine.FiniteObstruction
attribute [local instance] Classical.propDecidable
variable {T Q : Family}

theorem c32435 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    T {1, 2, 5} → T {1, 2, 8} → Q {3, 4, 6, 9} → False := by
  classical
  intro a39 a42 a302
  have u0_1 : T {0, 1, 2} := by
    by_contra hv
    exact c31203 h h0 hv
  exact c27205 h a302 u0_1 a39 a42

theorem c32443 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    Q {3, 4, 7, 8} → T {0, 2, 6} → T {0, 2, 9} → False := by
  classical
  intro a303 a12 a15
  have u0_1 : T {0, 1, 2} := by
    by_contra hv
    exact c31203 h h0 hv
  exact c27315 h a303 u0_1 a12 a15

theorem c32446 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    Q {3, 4, 7, 8} → T {1, 2, 9} → T {1, 2, 6} → False := by
  classical
  intro a303 a43 a40
  have u0_1 : T {0, 1, 2} := by
    by_contra hv
    exact c31203 h h0 hv
  exact c27347 h a303 u0_1 a40 a43

theorem c32447 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    Q {3, 4, 7, 9} → T {5, 6, 8} → False := by
  classical
  intro a304 a112
  have u0_1 : T {0, 1, 2} := by
    by_contra hv
    exact c31203 h h0 hv
  exact c27423 h a304 u0_1 a112

theorem c32457 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    Q {3, 4, 8, 9} → T {5, 6, 7} → False := by
  classical
  intro a305 a111
  have u0_1 : T {0, 1, 2} := by
    by_contra hv
    exact c31203 h h0 hv
  exact c27563 h a305 u0_1 a111

theorem c32460 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    Q {3, 4, 8, 9} → T {0, 1, 7} → T {0, 1, 6} → False := by
  classical
  intro a305 a6 a5
  have u0_1 : T {0, 1, 2} := by
    by_contra hv
    exact c31203 h h0 hv
  exact c27587 h a305 u0_1 a5 a6

theorem c32464 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    T {1, 2, 5} → Q {3, 4, 8, 9} → T {1, 2, 6} → False := by
  classical
  intro a39 a305 a40
  have u0_1 : T {0, 1, 2} := by
    by_contra hv
    exact c31203 h h0 hv
  exact c27623 h a305 u0_1 a39 a40

theorem c32467 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    Q {3, 5, 6, 7} → T {4, 8, 9} → False := by
  classical
  intro a306 a110
  have u0_1 : T {0, 1, 2} := by
    by_contra hv
    exact c31203 h h0 hv
  exact c27703 h a306 u0_1 a110

theorem c32475 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    Q {3, 5, 6, 7} → T {1, 2, 4} → T {1, 2, 9} → False := by
  classical
  intro a306 a38 a43
  have u0_1 : T {0, 1, 2} := by
    by_contra hv
    exact c31203 h h0 hv
  exact c27765 h a306 u0_1 a38 a43

theorem c32477 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    Q {3, 5, 6, 8} → T {4, 7, 9} → False := by
  classical
  intro a307 a109
  have u0_1 : T {0, 1, 2} := by
    by_contra hv
    exact c31203 h h0 hv
  exact c27843 h a307 u0_1 a109

theorem c32479 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    Q {3, 5, 6, 8} → T {0, 1, 4} → T {0, 1, 9} → False := by
  classical
  intro a307 a3 a8
  have u0_1 : T {0, 1, 2} := by
    by_contra hv
    exact c31203 h h0 hv
  exact c27865 h a307 u0_1 a3 a8

theorem c32482 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    Q {3, 5, 6, 8} → T {0, 2, 9} → T {0, 2, 4} → False := by
  classical
  intro a307 a15 a10
  have u0_1 : T {0, 1, 2} := by
    by_contra hv
    exact c31203 h h0 hv
  exact c27873 h a307 u0_1 a10 a15

theorem c32483 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    Q {3, 5, 6, 8} → T {0, 2, 9} → T {0, 2, 7} → False := by
  classical
  intro a307 a15 a13
  have u0_1 : T {0, 1, 2} := by
    by_contra hv
    exact c31203 h h0 hv
  exact c27875 h a307 u0_1 a13 a15

theorem c32485 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    Q {3, 5, 6, 8} → T {1, 2, 4} → T {1, 2, 9} → False := by
  classical
  intro a307 a38 a43
  have u0_1 : T {0, 1, 2} := by
    by_contra hv
    exact c31203 h h0 hv
  exact c27905 h a307 u0_1 a38 a43

theorem c32486 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    Q {3, 5, 6, 8} → T {1, 2, 9} → T {1, 2, 7} → False := by
  classical
  intro a307 a43 a41
  have u0_1 : T {0, 1, 2} := by
    by_contra hv
    exact c31203 h h0 hv
  exact c27907 h a307 u0_1 a41 a43

theorem c32487 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    Q {3, 5, 6, 9} → T {4, 7, 8} → False := by
  classical
  intro a308 a108
  have u0_1 : T {0, 1, 2} := by
    by_contra hv
    exact c31203 h h0 hv
  exact c27983 h a308 u0_1 a108

theorem c32496 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    Q {3, 5, 6, 9} → T {1, 2, 7} → T {1, 2, 8} → False := by
  classical
  intro a308 a41 a42
  have u0_1 : T {0, 1, 2} := by
    by_contra hv
    exact c31203 h h0 hv
  exact c28047 h a308 u0_1 a41 a42

theorem c32497 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    Q {3, 5, 7, 8} → T {4, 6, 9} → False := by
  classical
  intro a309 a107
  have u0_1 : T {0, 1, 2} := by
    by_contra hv
    exact c31203 h h0 hv
  exact c28123 h a309 u0_1 a107

theorem c32505 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    Q {3, 5, 7, 8} → T {1, 2, 4} → T {1, 2, 9} → False := by
  classical
  intro a309 a38 a43
  have u0_1 : T {0, 1, 2} := by
    by_contra hv
    exact c31203 h h0 hv
  exact c28185 h a309 u0_1 a38 a43

theorem c32506 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    Q {3, 5, 7, 8} → T {1, 2, 9} → T {1, 2, 6} → False := by
  classical
  intro a309 a43 a40
  have u0_1 : T {0, 1, 2} := by
    by_contra hv
    exact c31203 h h0 hv
  exact c28187 h a309 u0_1 a40 a43

theorem c32507 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    Q {3, 5, 7, 9} → T {4, 6, 8} → False := by
  classical
  intro a310 a106
  have u0_1 : T {0, 1, 2} := by
    by_contra hv
    exact c31203 h h0 hv
  exact c28263 h a310 u0_1 a106

theorem c32516 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    Q {3, 5, 7, 9} → T {1, 2, 8} → T {1, 2, 6} → False := by
  classical
  intro a310 a42 a40
  have u0_1 : T {0, 1, 2} := by
    by_contra hv
    exact c31203 h h0 hv
  exact c28327 h a310 u0_1 a40 a42

theorem c32517 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    Q {3, 5, 8, 9} → T {4, 6, 7} → False := by
  classical
  intro a311 a105
  have u0_1 : T {0, 1, 2} := by
    by_contra hv
    exact c31203 h h0 hv
  exact c28403 h a311 u0_1 a105

theorem c32518 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    T {0, 1, 4} → T {0, 1, 6} → Q {3, 5, 8, 9} → False := by
  classical
  intro a3 a5 a311
  have u0_1 : T {0, 1, 2} := by
    by_contra hv
    exact c31203 h h0 hv
  exact c28423 h a311 u0_1 a3 a5

theorem c32521 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    T {0, 2, 4} → T {0, 2, 6} → Q {3, 5, 8, 9} → False := by
  classical
  intro a10 a12 a311
  have u0_1 : T {0, 1, 2} := by
    by_contra hv
    exact c31203 h h0 hv
  exact c28431 h a311 u0_1 a10 a12

theorem c32523 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    T {0, 2, 7} → T {0, 2, 6} → Q {3, 5, 8, 9} → False := by
  classical
  intro a13 a12 a311
  have u0_1 : T {0, 1, 2} := by
    by_contra hv
    exact c31203 h h0 hv
  exact c28435 h a311 u0_1 a12 a13

theorem c32524 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    Q {3, 5, 8, 9} → T {1, 2, 4} → T {1, 2, 6} → False := by
  classical
  intro a311 a38 a40
  have u0_1 : T {0, 1, 2} := by
    by_contra hv
    exact c31203 h h0 hv
  exact c28463 h a311 u0_1 a38 a40

theorem c32525 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    T {1, 2, 7} → T {1, 2, 4} → Q {3, 5, 8, 9} → False := by
  classical
  intro a41 a38 a311
  have u0_1 : T {0, 1, 2} := by
    by_contra hv
    exact c31203 h h0 hv
  exact c28465 h a311 u0_1 a38 a41

theorem c32526 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    T {1, 2, 7} → Q {3, 5, 8, 9} → T {1, 2, 6} → False := by
  classical
  intro a41 a311 a40
  have u0_1 : T {0, 1, 2} := by
    by_contra hv
    exact c31203 h h0 hv
  exact c28467 h a311 u0_1 a40 a41

theorem c32527 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    Q {3, 6, 7, 8} → T {4, 5, 9} → False := by
  classical
  intro a312 a104
  have u0_1 : T {0, 1, 2} := by
    by_contra hv
    exact c31203 h h0 hv
  exact c28543 h a312 u0_1 a104

theorem c32534 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    Q {3, 6, 7, 8} → T {1, 2, 5} → T {1, 2, 4} → False := by
  classical
  intro a312 a39 a38
  have u0_1 : T {0, 1, 2} := by
    by_contra hv
    exact c31203 h h0 hv
  exact c28603 h a312 u0_1 a38 a39

theorem c32535 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    Q {3, 6, 7, 8} → T {1, 2, 4} → T {1, 2, 9} → False := by
  classical
  intro a312 a38 a43
  have u0_1 : T {0, 1, 2} := by
    by_contra hv
    exact c31203 h h0 hv
  exact c28605 h a312 u0_1 a38 a43

theorem c32536 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    Q {3, 6, 7, 8} → T {1, 2, 5} → T {1, 2, 9} → False := by
  classical
  intro a312 a39 a43
  have u0_1 : T {0, 1, 2} := by
    by_contra hv
    exact c31203 h h0 hv
  exact c28607 h a312 u0_1 a39 a43

theorem c32537 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    Q {3, 6, 7, 9} → T {4, 5, 8} → False := by
  classical
  intro a313 a103
  have u0_1 : T {0, 1, 2} := by
    by_contra hv
    exact c31203 h h0 hv
  exact c28683 h a313 u0_1 a103

theorem c32546 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    T {1, 2, 5} → T {1, 2, 8} → Q {3, 6, 7, 9} → False := by
  classical
  intro a39 a42 a313
  have u0_1 : T {0, 1, 2} := by
    by_contra hv
    exact c31203 h h0 hv
  exact c28747 h a313 u0_1 a39 a42

theorem c32547 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    Q {3, 6, 8, 9} → T {4, 5, 7} → False := by
  classical
  intro a314 a102
  have u0_1 : T {0, 1, 2} := by
    by_contra hv
    exact c31203 h h0 hv
  exact c28823 h a314 u0_1 a102

theorem c32549 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    Q {3, 6, 8, 9} → T {0, 1, 7} → T {0, 1, 4} → False := by
  classical
  intro a314 a6 a3
  have u0_1 : T {0, 1, 2} := by
    by_contra hv
    exact c31203 h h0 hv
  exact c28845 h a314 u0_1 a3 a6

theorem c32552 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    Q {3, 6, 8, 9} → T {0, 2, 7} → T {0, 2, 4} → False := by
  classical
  intro a314 a13 a10
  have u0_1 : T {0, 1, 2} := by
    by_contra hv
    exact c31203 h h0 hv
  exact c28853 h a314 u0_1 a10 a13

theorem c32556 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    Q {3, 6, 8, 9} → T {1, 2, 7} → T {1, 2, 5} → False := by
  classical
  intro a314 a41 a39
  have u0_1 : T {0, 1, 2} := by
    by_contra hv
    exact c31203 h h0 hv
  exact c28887 h a314 u0_1 a39 a41

theorem c32557 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    Q {3, 7, 8, 9} → T {4, 5, 6} → False := by
  classical
  intro a315 a101
  have u0_1 : T {0, 1, 2} := by
    by_contra hv
    exact c31203 h h0 hv
  exact c28963 h a315 u0_1 a101

theorem c32566 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    T {1, 2, 5} → Q {3, 7, 8, 9} → T {1, 2, 6} → False := by
  classical
  intro a39 a315 a40
  have u0_1 : T {0, 1, 2} := by
    by_contra hv
    exact c31203 h h0 hv
  exact c29027 h a315 u0_1 a39 a40

private theorem c32567 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    T {1, 2, 9} → ¬ Q {0, 1, 6, 7} → ¬ Q {0, 2, 6, 7} → T {0, 6, 7} → T {1, 2, 4} →
      ¬ Q {0, 3, 6, 7} → ¬ Q {0, 4, 6, 7} → ¬ Q {0, 6, 7, 9} → False := by
  classical
  intro a43 n143 n164 a31 a38 n179 n189 n202
  have u0_195 : ¬ Q {0, 5, 6, 7} := by
    intro hv
    exact c31869 h h0 hv a38 a43
  have u1_201 : ¬ Q {0, 6, 7, 8} := by
    intro hv
    exact c31929 h h0 hv a38 a43
  exact c452 h a31 n143 n164 n179 n189 u0_195 u1_201 n202

private theorem c32568 (h : TenSystem T Q) :
    ¬ T {1, 2, 9} → ¬ T {3, 6, 7} → ¬ Q {0, 1, 5, 8} → ¬ Q {0, 5, 7, 8} →
      ¬ Q {0, 2, 5, 8} → ¬ T {4, 6, 7} → T {0, 5, 8} → ¬ Q {0, 5, 6, 8} → False := by
  classical
  intro n43 n95 n141 n198 n162 n105 a29 n196
  have u0_177 : ¬ Q {0, 3, 5, 8} := by
    intro hv
    exact c9648 h hv n43 n105
  have u1_187 : ¬ Q {0, 4, 5, 8} := by
    intro hv
    exact c11048 h hv n43 n95
  have u2_200 : Q {0, 5, 8, 9} := by
    by_contra hv
    exact c31443 h u0_177 n141 a29 hv n162 n198 n196
  exact c436 h u2_200 n141 n162 u0_177 u1_187 n196 n198

theorem c32569 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    T {0, 6, 7} → ¬ T {3, 6, 7} → T {5, 8, 9} → ¬ T {1, 3, 9} → Q {3, 4, 7, 9} → False := by
  classical
  intro a31 n95 a116 n49 a304
  have u0_109 : T {4, 7, 9} := by
    by_contra hv
    exact c1629 h a304 hv
  have u1_196 : ¬ Q {0, 5, 6, 8} := by
    intro hv
    exact c31877 h h0 hv u0_109
  have u2_29 : T {0, 5, 8} := by
    by_contra hv
    exact c31527 h h0 hv n49 a304
  have u3_105 : ¬ T {4, 6, 7} := by
    intro hv
    exact c31636 h h0 hv a116
  have u4_162 : ¬ Q {0, 2, 5, 8} := by
    intro hv
    exact c7548 h hv n49 u3_105
  have u5_118 : ¬ T {6, 7, 9} := by
    intro hv
    exact c31520 h h0 hv a304
  have u6_103 : T {4, 5, 8} := by
    by_contra hv
    exact c31631 h h0 hv u5_118
  have u7_114 : ¬ T {5, 7, 8} := by
    intro hv
    exact c31708 h h0 hv a116 u6_103
  have u8_198 : ¬ Q {0, 5, 7, 8} := by
    intro hv
    exact c1698 h hv u7_114
  have u9_90 : T {3, 4, 9} := by
    by_contra hv
    exact c1348 h a304 hv
  have u10_107 : T {4, 6, 9} := by
    by_contra hv
    exact c31639 h h0 hv u7_114
  have u11_141 : ¬ Q {0, 1, 5, 8} := by
    intro hv
    exact c4717 h hv u9_90 u10_107 u0_109
  have u12_43 : T {1, 2, 9} := by
    by_contra hv
    exact c32568 h hv n95 u11_141 u8_198 u4_162 u3_105 u2_29 u1_196
  have u13_38 : T {1, 2, 4} := by
    by_contra hv
    exact c31530 h h0 hv n95 u11_141 u8_198 u4_162 u2_29 a304
  have u14_179 : ¬ Q {0, 3, 6, 7} := by
    intro hv
    exact c1413 h hv n95
  have u15_127 : ¬ Q {0, 1, 2, 9} := by
    intro hv
    exact c31531 h h0 hv a116 n49 a304
  have u16_117 : T {6, 7, 8} := by
    by_contra hv
    exact c31723 h h0 hv u3_105 u5_118
  have u17_123 : ¬ Q {0, 1, 2, 5} := by
    intro hv
    exact c2089 h hv u9_90 u16_117
  have u18_299 : ¬ Q {3, 4, 5, 9} := by
    intro hv
    exact c32397 h h0 hv u16_117
  have u19_111 : T {5, 6, 7} := by
    by_contra hv
    exact c31721 h h0 hv u3_105 u5_118
  have u20_126 : ¬ Q {0, 1, 2, 8} := by
    intro hv
    exact c2509 h hv u9_90 u19_111
  have u21_305 : ¬ Q {3, 4, 8, 9} := by
    intro hv
    exact c32457 h h0 hv u19_111
  have u22_40 : ¬ T {1, 2, 6} := by
    intro hv
    exact c27439 h a304 u2_29 hv
  have u23_174 : ¬ Q {0, 3, 4, 9} := by
    intro hv
    exact c9224 h hv u22_40 u7_114
  have u24_189 : ¬ Q {0, 4, 6, 7} := by
    intro hv
    exact c31807 h h0 hv a116
  have u25_230 : ¬ Q {1, 3, 4, 9} := by
    intro hv
    exact c727 h hv n49
  have u26_99 : T {3, 7, 9} := by
    by_contra hv
    exact c1479 h a304 hv
  have u27_124 : ¬ Q {0, 1, 2, 6} := by
    intro hv
    exact c2239 h hv u26_99 u6_103
  have u28_202 : ¬ Q {0, 6, 7, 9} := by
    intro hv
    exact c1758 h hv u5_118
  have u29_265 : ¬ Q {2, 3, 4, 9} := by
    intro hv
    exact c22083 h hv a31 u19_111 u16_117
  have u30_302 : Q {3, 4, 6, 9} := by
    by_contra hv
    exact c1349 h a304 u23_174 u25_230 u29_265 u18_299 hv u21_305
  have u31_87 : T {3, 4, 6} := by
    by_contra hv
    exact c1305 h u30_302 hv
  have u32_97 : T {3, 6, 9} := by
    by_contra hv
    exact c1449 h u30_302 hv
  have u33_125 : ¬ Q {0, 1, 2, 7} := by
    intro hv
    exact c2365 h hv u31_87 a116
  have u34_122 : Q {0, 1, 2, 4} := by
    by_contra hv
    exact c31532 h h0 hv u33_125 u27_124 u15_127 u17_123 u20_126
  have u35_100 : ¬ T {3, 8, 9} := by
    intro hv
    exact c2001 h u34_122 u32_97 u26_99 hv
  have u36_94 : ¬ T {3, 5, 9} := by
    intro hv
    exact c1949 h u34_122 hv u16_117
  have u37_93 : T {3, 5, 8} := by
    by_contra hv
    exact c1946 h u34_122 hv u5_118
  have u38_164 : ¬ Q {0, 2, 6, 7} := by
    intro hv
    exact c7910 h hv n49 u36_94 u35_100
  have u39_143 : ¬ Q {0, 1, 6, 7} := by
    intro hv
    exact c5005 h hv u37_93 u6_103 a116
  exact c32567 h h0 u12_43 u39_143 u38_164 a31 u13_38 u14_179 u24_189 u28_202

end BorsukNine.FiniteObstruction

end OAI
