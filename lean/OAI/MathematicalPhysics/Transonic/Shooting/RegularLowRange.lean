import OAI.MathematicalPhysics.Transonic.Shooting.RegularGlobalRange
import OAI.MathematicalPhysics.Transonic.Shooting.RegularLowEndpoint

namespace OAI

section

namespace SepticProfile.RegularLowData
open Set IntegerPolynomial
theorem range_0 {u : ℝ → ℝ} (hud : ∀ t ∈ Icc (0:ℝ) (9/100), HasDerivWithinAt u
    (globalField (SN/S) (KN/K) t (u t)) (Icc 0 (9/100)) t)
    (hu : u (startTime R step0) ∈ Icc ((head step0.lo:ℝ)/Q) ((head step0.hi:ℝ)/Q)) :
    ∀ t ∈ Icc (startTime R step0) (stopTime R step15), u t ∈ Icc (0:ℝ) (999/1000) := by
  intro t ht
  have ht0 := ht.1
  by_cases hstop0 : t ≤ stopTime R step0
  · exact global_step_range S_pos K_pos R_pos Q_pos sigma_mem cert0 hud hu t ⟨ht0,hstop0⟩
  have h0 := global_step_endpoint S_pos K_pos R_pos Q_pos sigma_mem cert0 hud hu
  have hu1 := join_bound Q_pos join1 h0
  have ht1 : startTime R step1 ≤ t := by
    rw [start_eq_stop join1.1]
    exact (lt_of_not_ge hstop0).le
  by_cases hstop1 : t ≤ stopTime R step1
  · exact global_step_range S_pos K_pos R_pos Q_pos sigma_mem cert1 hud hu1 t ⟨ht1,hstop1⟩
  have h1 := global_step_endpoint S_pos K_pos R_pos Q_pos sigma_mem cert1 hud hu1
  have hu2 := join_bound Q_pos join2 h1
  have ht2 : startTime R step2 ≤ t := by
    rw [start_eq_stop join2.1]
    exact (lt_of_not_ge hstop1).le
  by_cases hstop2 : t ≤ stopTime R step2
  · exact global_step_range S_pos K_pos R_pos Q_pos sigma_mem cert2 hud hu2 t ⟨ht2,hstop2⟩
  have h2 := global_step_endpoint S_pos K_pos R_pos Q_pos sigma_mem cert2 hud hu2
  have hu3 := join_bound Q_pos join3 h2
  have ht3 : startTime R step3 ≤ t := by
    rw [start_eq_stop join3.1]
    exact (lt_of_not_ge hstop2).le
  by_cases hstop3 : t ≤ stopTime R step3
  · exact global_step_range S_pos K_pos R_pos Q_pos sigma_mem cert3 hud hu3 t ⟨ht3,hstop3⟩
  have h3 := global_step_endpoint S_pos K_pos R_pos Q_pos sigma_mem cert3 hud hu3
  have hu4 := join_bound Q_pos join4 h3
  have ht4 : startTime R step4 ≤ t := by
    rw [start_eq_stop join4.1]
    exact (lt_of_not_ge hstop3).le
  by_cases hstop4 : t ≤ stopTime R step4
  · exact global_step_range S_pos K_pos R_pos Q_pos sigma_mem cert4 hud hu4 t ⟨ht4,hstop4⟩
  have h4 := global_step_endpoint S_pos K_pos R_pos Q_pos sigma_mem cert4 hud hu4
  have hu5 := join_bound Q_pos join5 h4
  have ht5 : startTime R step5 ≤ t := by
    rw [start_eq_stop join5.1]
    exact (lt_of_not_ge hstop4).le
  by_cases hstop5 : t ≤ stopTime R step5
  · exact global_step_range S_pos K_pos R_pos Q_pos sigma_mem cert5 hud hu5 t ⟨ht5,hstop5⟩
  have h5 := global_step_endpoint S_pos K_pos R_pos Q_pos sigma_mem cert5 hud hu5
  have hu6 := join_bound Q_pos join6 h5
  have ht6 : startTime R step6 ≤ t := by
    rw [start_eq_stop join6.1]
    exact (lt_of_not_ge hstop5).le
  by_cases hstop6 : t ≤ stopTime R step6
  · exact global_step_range S_pos K_pos R_pos Q_pos sigma_mem cert6 hud hu6 t ⟨ht6,hstop6⟩
  have h6 := global_step_endpoint S_pos K_pos R_pos Q_pos sigma_mem cert6 hud hu6
  have hu7 := join_bound Q_pos join7 h6
  have ht7 : startTime R step7 ≤ t := by
    rw [start_eq_stop join7.1]
    exact (lt_of_not_ge hstop6).le
  by_cases hstop7 : t ≤ stopTime R step7
  · exact global_step_range S_pos K_pos R_pos Q_pos sigma_mem cert7 hud hu7 t ⟨ht7,hstop7⟩
  have h7 := global_step_endpoint S_pos K_pos R_pos Q_pos sigma_mem cert7 hud hu7
  have hu8 := join_bound Q_pos join8 h7
  have ht8 : startTime R step8 ≤ t := by
    rw [start_eq_stop join8.1]
    exact (lt_of_not_ge hstop7).le
  by_cases hstop8 : t ≤ stopTime R step8
  · exact global_step_range S_pos K_pos R_pos Q_pos sigma_mem cert8 hud hu8 t ⟨ht8,hstop8⟩
  have h8 := global_step_endpoint S_pos K_pos R_pos Q_pos sigma_mem cert8 hud hu8
  have hu9 := join_bound Q_pos join9 h8
  have ht9 : startTime R step9 ≤ t := by
    rw [start_eq_stop join9.1]
    exact (lt_of_not_ge hstop8).le
  by_cases hstop9 : t ≤ stopTime R step9
  · exact global_step_range S_pos K_pos R_pos Q_pos sigma_mem cert9 hud hu9 t ⟨ht9,hstop9⟩
  have h9 := global_step_endpoint S_pos K_pos R_pos Q_pos sigma_mem cert9 hud hu9
  have hu10 := join_bound Q_pos join10 h9
  have ht10 : startTime R step10 ≤ t := by
    rw [start_eq_stop join10.1]
    exact (lt_of_not_ge hstop9).le
  by_cases hstop10 : t ≤ stopTime R step10
  · exact global_step_range S_pos K_pos R_pos Q_pos sigma_mem cert10 hud hu10 t ⟨ht10,hstop10⟩
  have h10 := global_step_endpoint S_pos K_pos R_pos Q_pos sigma_mem cert10 hud hu10
  have hu11 := join_bound Q_pos join11 h10
  have ht11 : startTime R step11 ≤ t := by
    rw [start_eq_stop join11.1]
    exact (lt_of_not_ge hstop10).le
  by_cases hstop11 : t ≤ stopTime R step11
  · exact global_step_range S_pos K_pos R_pos Q_pos sigma_mem cert11 hud hu11 t ⟨ht11,hstop11⟩
  have h11 := global_step_endpoint S_pos K_pos R_pos Q_pos sigma_mem cert11 hud hu11
  have hu12 := join_bound Q_pos join12 h11
  have ht12 : startTime R step12 ≤ t := by
    rw [start_eq_stop join12.1]
    exact (lt_of_not_ge hstop11).le
  by_cases hstop12 : t ≤ stopTime R step12
  · exact global_step_range S_pos K_pos R_pos Q_pos sigma_mem cert12 hud hu12 t ⟨ht12,hstop12⟩
  have h12 := global_step_endpoint S_pos K_pos R_pos Q_pos sigma_mem cert12 hud hu12
  have hu13 := join_bound Q_pos join13 h12
  have ht13 : startTime R step13 ≤ t := by
    rw [start_eq_stop join13.1]
    exact (lt_of_not_ge hstop12).le
  by_cases hstop13 : t ≤ stopTime R step13
  · exact global_step_range S_pos K_pos R_pos Q_pos sigma_mem cert13 hud hu13 t ⟨ht13,hstop13⟩
  have h13 := global_step_endpoint S_pos K_pos R_pos Q_pos sigma_mem cert13 hud hu13
  have hu14 := join_bound Q_pos join14 h13
  have ht14 : startTime R step14 ≤ t := by
    rw [start_eq_stop join14.1]
    exact (lt_of_not_ge hstop13).le
  by_cases hstop14 : t ≤ stopTime R step14
  · exact global_step_range S_pos K_pos R_pos Q_pos sigma_mem cert14 hud hu14 t ⟨ht14,hstop14⟩
  have h14 := global_step_endpoint S_pos K_pos R_pos Q_pos sigma_mem cert14 hud hu14
  have hu15 := join_bound Q_pos join15 h14
  have ht15 : startTime R step15 ≤ t := by
    rw [start_eq_stop join15.1]
    exact (lt_of_not_ge hstop14).le
  exact global_step_range S_pos K_pos R_pos Q_pos sigma_mem cert15 hud hu15 t ⟨ht15,ht.2⟩
theorem range_16 {u : ℝ → ℝ} (hud : ∀ t ∈ Icc (0:ℝ) (9/100), HasDerivWithinAt u
    (globalField (SN/S) (KN/K) t (u t)) (Icc 0 (9/100)) t)
    (hu : u (startTime R step16) ∈ Icc ((head step16.lo:ℝ)/Q) ((head step16.hi:ℝ)/Q)) :
    ∀ t ∈ Icc (startTime R step16) (stopTime R step31), u t ∈ Icc (0:ℝ) (999/1000) := by
  intro t ht
  have ht16 := ht.1
  by_cases hstop16 : t ≤ stopTime R step16
  · exact global_step_range S_pos K_pos R_pos Q_pos sigma_mem cert16 hud hu t ⟨ht16,hstop16⟩
  have h16 := global_step_endpoint S_pos K_pos R_pos Q_pos sigma_mem cert16 hud hu
  have hu17 := join_bound Q_pos join17 h16
  have ht17 : startTime R step17 ≤ t := by
    rw [start_eq_stop join17.1]
    exact (lt_of_not_ge hstop16).le
  by_cases hstop17 : t ≤ stopTime R step17
  · exact global_step_range S_pos K_pos R_pos Q_pos sigma_mem cert17 hud hu17 t ⟨ht17,hstop17⟩
  have h17 := global_step_endpoint S_pos K_pos R_pos Q_pos sigma_mem cert17 hud hu17
  have hu18 := join_bound Q_pos join18 h17
  have ht18 : startTime R step18 ≤ t := by
    rw [start_eq_stop join18.1]
    exact (lt_of_not_ge hstop17).le
  by_cases hstop18 : t ≤ stopTime R step18
  · exact global_step_range S_pos K_pos R_pos Q_pos sigma_mem cert18 hud hu18 t ⟨ht18,hstop18⟩
  have h18 := global_step_endpoint S_pos K_pos R_pos Q_pos sigma_mem cert18 hud hu18
  have hu19 := join_bound Q_pos join19 h18
  have ht19 : startTime R step19 ≤ t := by
    rw [start_eq_stop join19.1]
    exact (lt_of_not_ge hstop18).le
  by_cases hstop19 : t ≤ stopTime R step19
  · exact global_step_range S_pos K_pos R_pos Q_pos sigma_mem cert19 hud hu19 t ⟨ht19,hstop19⟩
  have h19 := global_step_endpoint S_pos K_pos R_pos Q_pos sigma_mem cert19 hud hu19
  have hu20 := join_bound Q_pos join20 h19
  have ht20 : startTime R step20 ≤ t := by
    rw [start_eq_stop join20.1]
    exact (lt_of_not_ge hstop19).le
  by_cases hstop20 : t ≤ stopTime R step20
  · exact global_step_range S_pos K_pos R_pos Q_pos sigma_mem cert20 hud hu20 t ⟨ht20,hstop20⟩
  have h20 := global_step_endpoint S_pos K_pos R_pos Q_pos sigma_mem cert20 hud hu20
  have hu21 := join_bound Q_pos join21 h20
  have ht21 : startTime R step21 ≤ t := by
    rw [start_eq_stop join21.1]
    exact (lt_of_not_ge hstop20).le
  by_cases hstop21 : t ≤ stopTime R step21
  · exact global_step_range S_pos K_pos R_pos Q_pos sigma_mem cert21 hud hu21 t ⟨ht21,hstop21⟩
  have h21 := global_step_endpoint S_pos K_pos R_pos Q_pos sigma_mem cert21 hud hu21
  have hu22 := join_bound Q_pos join22 h21
  have ht22 : startTime R step22 ≤ t := by
    rw [start_eq_stop join22.1]
    exact (lt_of_not_ge hstop21).le
  by_cases hstop22 : t ≤ stopTime R step22
  · exact global_step_range S_pos K_pos R_pos Q_pos sigma_mem cert22 hud hu22 t ⟨ht22,hstop22⟩
  have h22 := global_step_endpoint S_pos K_pos R_pos Q_pos sigma_mem cert22 hud hu22
  have hu23 := join_bound Q_pos join23 h22
  have ht23 : startTime R step23 ≤ t := by
    rw [start_eq_stop join23.1]
    exact (lt_of_not_ge hstop22).le
  by_cases hstop23 : t ≤ stopTime R step23
  · exact global_step_range S_pos K_pos R_pos Q_pos sigma_mem cert23 hud hu23 t ⟨ht23,hstop23⟩
  have h23 := global_step_endpoint S_pos K_pos R_pos Q_pos sigma_mem cert23 hud hu23
  have hu24 := join_bound Q_pos join24 h23
  have ht24 : startTime R step24 ≤ t := by
    rw [start_eq_stop join24.1]
    exact (lt_of_not_ge hstop23).le
  by_cases hstop24 : t ≤ stopTime R step24
  · exact global_step_range S_pos K_pos R_pos Q_pos sigma_mem cert24 hud hu24 t ⟨ht24,hstop24⟩
  have h24 := global_step_endpoint S_pos K_pos R_pos Q_pos sigma_mem cert24 hud hu24
  have hu25 := join_bound Q_pos join25 h24
  have ht25 : startTime R step25 ≤ t := by
    rw [start_eq_stop join25.1]
    exact (lt_of_not_ge hstop24).le
  by_cases hstop25 : t ≤ stopTime R step25
  · exact global_step_range S_pos K_pos R_pos Q_pos sigma_mem cert25 hud hu25 t ⟨ht25,hstop25⟩
  have h25 := global_step_endpoint S_pos K_pos R_pos Q_pos sigma_mem cert25 hud hu25
  have hu26 := join_bound Q_pos join26 h25
  have ht26 : startTime R step26 ≤ t := by
    rw [start_eq_stop join26.1]
    exact (lt_of_not_ge hstop25).le
  by_cases hstop26 : t ≤ stopTime R step26
  · exact global_step_range S_pos K_pos R_pos Q_pos sigma_mem cert26 hud hu26 t ⟨ht26,hstop26⟩
  have h26 := global_step_endpoint S_pos K_pos R_pos Q_pos sigma_mem cert26 hud hu26
  have hu27 := join_bound Q_pos join27 h26
  have ht27 : startTime R step27 ≤ t := by
    rw [start_eq_stop join27.1]
    exact (lt_of_not_ge hstop26).le
  by_cases hstop27 : t ≤ stopTime R step27
  · exact global_step_range S_pos K_pos R_pos Q_pos sigma_mem cert27 hud hu27 t ⟨ht27,hstop27⟩
  have h27 := global_step_endpoint S_pos K_pos R_pos Q_pos sigma_mem cert27 hud hu27
  have hu28 := join_bound Q_pos join28 h27
  have ht28 : startTime R step28 ≤ t := by
    rw [start_eq_stop join28.1]
    exact (lt_of_not_ge hstop27).le
  by_cases hstop28 : t ≤ stopTime R step28
  · exact global_step_range S_pos K_pos R_pos Q_pos sigma_mem cert28 hud hu28 t ⟨ht28,hstop28⟩
  have h28 := global_step_endpoint S_pos K_pos R_pos Q_pos sigma_mem cert28 hud hu28
  have hu29 := join_bound Q_pos join29 h28
  have ht29 : startTime R step29 ≤ t := by
    rw [start_eq_stop join29.1]
    exact (lt_of_not_ge hstop28).le
  by_cases hstop29 : t ≤ stopTime R step29
  · exact global_step_range S_pos K_pos R_pos Q_pos sigma_mem cert29 hud hu29 t ⟨ht29,hstop29⟩
  have h29 := global_step_endpoint S_pos K_pos R_pos Q_pos sigma_mem cert29 hud hu29
  have hu30 := join_bound Q_pos join30 h29
  have ht30 : startTime R step30 ≤ t := by
    rw [start_eq_stop join30.1]
    exact (lt_of_not_ge hstop29).le
  by_cases hstop30 : t ≤ stopTime R step30
  · exact global_step_range S_pos K_pos R_pos Q_pos sigma_mem cert30 hud hu30 t ⟨ht30,hstop30⟩
  have h30 := global_step_endpoint S_pos K_pos R_pos Q_pos sigma_mem cert30 hud hu30
  have hu31 := join_bound Q_pos join31 h30
  have ht31 : startTime R step31 ≤ t := by
    rw [start_eq_stop join31.1]
    exact (lt_of_not_ge hstop30).le
  exact global_step_range S_pos K_pos R_pos Q_pos sigma_mem cert31 hud hu31 t ⟨ht31,ht.2⟩
theorem range_32 {u : ℝ → ℝ} (hud : ∀ t ∈ Icc (0:ℝ) (9/100), HasDerivWithinAt u
    (globalField (SN/S) (KN/K) t (u t)) (Icc 0 (9/100)) t)
    (hu : u (startTime R step32) ∈ Icc ((head step32.lo:ℝ)/Q) ((head step32.hi:ℝ)/Q)) :
    ∀ t ∈ Icc (startTime R step32) (stopTime R step47), u t ∈ Icc (0:ℝ) (999/1000) := by
  intro t ht
  have ht32 := ht.1
  by_cases hstop32 : t ≤ stopTime R step32
  · exact global_step_range S_pos K_pos R_pos Q_pos sigma_mem cert32 hud hu t ⟨ht32,hstop32⟩
  have h32 := global_step_endpoint S_pos K_pos R_pos Q_pos sigma_mem cert32 hud hu
  have hu33 := join_bound Q_pos join33 h32
  have ht33 : startTime R step33 ≤ t := by
    rw [start_eq_stop join33.1]
    exact (lt_of_not_ge hstop32).le
  by_cases hstop33 : t ≤ stopTime R step33
  · exact global_step_range S_pos K_pos R_pos Q_pos sigma_mem cert33 hud hu33 t ⟨ht33,hstop33⟩
  have h33 := global_step_endpoint S_pos K_pos R_pos Q_pos sigma_mem cert33 hud hu33
  have hu34 := join_bound Q_pos join34 h33
  have ht34 : startTime R step34 ≤ t := by
    rw [start_eq_stop join34.1]
    exact (lt_of_not_ge hstop33).le
  by_cases hstop34 : t ≤ stopTime R step34
  · exact global_step_range S_pos K_pos R_pos Q_pos sigma_mem cert34 hud hu34 t ⟨ht34,hstop34⟩
  have h34 := global_step_endpoint S_pos K_pos R_pos Q_pos sigma_mem cert34 hud hu34
  have hu35 := join_bound Q_pos join35 h34
  have ht35 : startTime R step35 ≤ t := by
    rw [start_eq_stop join35.1]
    exact (lt_of_not_ge hstop34).le
  by_cases hstop35 : t ≤ stopTime R step35
  · exact global_step_range S_pos K_pos R_pos Q_pos sigma_mem cert35 hud hu35 t ⟨ht35,hstop35⟩
  have h35 := global_step_endpoint S_pos K_pos R_pos Q_pos sigma_mem cert35 hud hu35
  have hu36 := join_bound Q_pos join36 h35
  have ht36 : startTime R step36 ≤ t := by
    rw [start_eq_stop join36.1]
    exact (lt_of_not_ge hstop35).le
  by_cases hstop36 : t ≤ stopTime R step36
  · exact global_step_range S_pos K_pos R_pos Q_pos sigma_mem cert36 hud hu36 t ⟨ht36,hstop36⟩
  have h36 := global_step_endpoint S_pos K_pos R_pos Q_pos sigma_mem cert36 hud hu36
  have hu37 := join_bound Q_pos join37 h36
  have ht37 : startTime R step37 ≤ t := by
    rw [start_eq_stop join37.1]
    exact (lt_of_not_ge hstop36).le
  by_cases hstop37 : t ≤ stopTime R step37
  · exact global_step_range S_pos K_pos R_pos Q_pos sigma_mem cert37 hud hu37 t ⟨ht37,hstop37⟩
  have h37 := global_step_endpoint S_pos K_pos R_pos Q_pos sigma_mem cert37 hud hu37
  have hu38 := join_bound Q_pos join38 h37
  have ht38 : startTime R step38 ≤ t := by
    rw [start_eq_stop join38.1]
    exact (lt_of_not_ge hstop37).le
  by_cases hstop38 : t ≤ stopTime R step38
  · exact global_step_range S_pos K_pos R_pos Q_pos sigma_mem cert38 hud hu38 t ⟨ht38,hstop38⟩
  have h38 := global_step_endpoint S_pos K_pos R_pos Q_pos sigma_mem cert38 hud hu38
  have hu39 := join_bound Q_pos join39 h38
  have ht39 : startTime R step39 ≤ t := by
    rw [start_eq_stop join39.1]
    exact (lt_of_not_ge hstop38).le
  by_cases hstop39 : t ≤ stopTime R step39
  · exact global_step_range S_pos K_pos R_pos Q_pos sigma_mem cert39 hud hu39 t ⟨ht39,hstop39⟩
  have h39 := global_step_endpoint S_pos K_pos R_pos Q_pos sigma_mem cert39 hud hu39
  have hu40 := join_bound Q_pos join40 h39
  have ht40 : startTime R step40 ≤ t := by
    rw [start_eq_stop join40.1]
    exact (lt_of_not_ge hstop39).le
  by_cases hstop40 : t ≤ stopTime R step40
  · exact global_step_range S_pos K_pos R_pos Q_pos sigma_mem cert40 hud hu40 t ⟨ht40,hstop40⟩
  have h40 := global_step_endpoint S_pos K_pos R_pos Q_pos sigma_mem cert40 hud hu40
  have hu41 := join_bound Q_pos join41 h40
  have ht41 : startTime R step41 ≤ t := by
    rw [start_eq_stop join41.1]
    exact (lt_of_not_ge hstop40).le
  by_cases hstop41 : t ≤ stopTime R step41
  · exact global_step_range S_pos K_pos R_pos Q_pos sigma_mem cert41 hud hu41 t ⟨ht41,hstop41⟩
  have h41 := global_step_endpoint S_pos K_pos R_pos Q_pos sigma_mem cert41 hud hu41
  have hu42 := join_bound Q_pos join42 h41
  have ht42 : startTime R step42 ≤ t := by
    rw [start_eq_stop join42.1]
    exact (lt_of_not_ge hstop41).le
  by_cases hstop42 : t ≤ stopTime R step42
  · exact global_step_range S_pos K_pos R_pos Q_pos sigma_mem cert42 hud hu42 t ⟨ht42,hstop42⟩
  have h42 := global_step_endpoint S_pos K_pos R_pos Q_pos sigma_mem cert42 hud hu42
  have hu43 := join_bound Q_pos join43 h42
  have ht43 : startTime R step43 ≤ t := by
    rw [start_eq_stop join43.1]
    exact (lt_of_not_ge hstop42).le
  by_cases hstop43 : t ≤ stopTime R step43
  · exact global_step_range S_pos K_pos R_pos Q_pos sigma_mem cert43 hud hu43 t ⟨ht43,hstop43⟩
  have h43 := global_step_endpoint S_pos K_pos R_pos Q_pos sigma_mem cert43 hud hu43
  have hu44 := join_bound Q_pos join44 h43
  have ht44 : startTime R step44 ≤ t := by
    rw [start_eq_stop join44.1]
    exact (lt_of_not_ge hstop43).le
  by_cases hstop44 : t ≤ stopTime R step44
  · exact global_step_range S_pos K_pos R_pos Q_pos sigma_mem cert44 hud hu44 t ⟨ht44,hstop44⟩
  have h44 := global_step_endpoint S_pos K_pos R_pos Q_pos sigma_mem cert44 hud hu44
  have hu45 := join_bound Q_pos join45 h44
  have ht45 : startTime R step45 ≤ t := by
    rw [start_eq_stop join45.1]
    exact (lt_of_not_ge hstop44).le
  by_cases hstop45 : t ≤ stopTime R step45
  · exact global_step_range S_pos K_pos R_pos Q_pos sigma_mem cert45 hud hu45 t ⟨ht45,hstop45⟩
  have h45 := global_step_endpoint S_pos K_pos R_pos Q_pos sigma_mem cert45 hud hu45
  have hu46 := join_bound Q_pos join46 h45
  have ht46 : startTime R step46 ≤ t := by
    rw [start_eq_stop join46.1]
    exact (lt_of_not_ge hstop45).le
  by_cases hstop46 : t ≤ stopTime R step46
  · exact global_step_range S_pos K_pos R_pos Q_pos sigma_mem cert46 hud hu46 t ⟨ht46,hstop46⟩
  have h46 := global_step_endpoint S_pos K_pos R_pos Q_pos sigma_mem cert46 hud hu46
  have hu47 := join_bound Q_pos join47 h46
  have ht47 : startTime R step47 ≤ t := by
    rw [start_eq_stop join47.1]
    exact (lt_of_not_ge hstop46).le
  exact global_step_range S_pos K_pos R_pos Q_pos sigma_mem cert47 hud hu47 t ⟨ht47,ht.2⟩
theorem range_48 {u : ℝ → ℝ} (hud : ∀ t ∈ Icc (0:ℝ) (9/100), HasDerivWithinAt u
    (globalField (SN/S) (KN/K) t (u t)) (Icc 0 (9/100)) t)
    (hu : u (startTime R step48) ∈ Icc ((head step48.lo:ℝ)/Q) ((head step48.hi:ℝ)/Q)) :
    ∀ t ∈ Icc (startTime R step48) (stopTime R step63), u t ∈ Icc (0:ℝ) (999/1000) := by
  intro t ht
  have ht48 := ht.1
  by_cases hstop48 : t ≤ stopTime R step48
  · exact global_step_range S_pos K_pos R_pos Q_pos sigma_mem cert48 hud hu t ⟨ht48,hstop48⟩
  have h48 := global_step_endpoint S_pos K_pos R_pos Q_pos sigma_mem cert48 hud hu
  have hu49 := join_bound Q_pos join49 h48
  have ht49 : startTime R step49 ≤ t := by
    rw [start_eq_stop join49.1]
    exact (lt_of_not_ge hstop48).le
  by_cases hstop49 : t ≤ stopTime R step49
  · exact global_step_range S_pos K_pos R_pos Q_pos sigma_mem cert49 hud hu49 t ⟨ht49,hstop49⟩
  have h49 := global_step_endpoint S_pos K_pos R_pos Q_pos sigma_mem cert49 hud hu49
  have hu50 := join_bound Q_pos join50 h49
  have ht50 : startTime R step50 ≤ t := by
    rw [start_eq_stop join50.1]
    exact (lt_of_not_ge hstop49).le
  by_cases hstop50 : t ≤ stopTime R step50
  · exact global_step_range S_pos K_pos R_pos Q_pos sigma_mem cert50 hud hu50 t ⟨ht50,hstop50⟩
  have h50 := global_step_endpoint S_pos K_pos R_pos Q_pos sigma_mem cert50 hud hu50
  have hu51 := join_bound Q_pos join51 h50
  have ht51 : startTime R step51 ≤ t := by
    rw [start_eq_stop join51.1]
    exact (lt_of_not_ge hstop50).le
  by_cases hstop51 : t ≤ stopTime R step51
  · exact global_step_range S_pos K_pos R_pos Q_pos sigma_mem cert51 hud hu51 t ⟨ht51,hstop51⟩
  have h51 := global_step_endpoint S_pos K_pos R_pos Q_pos sigma_mem cert51 hud hu51
  have hu52 := join_bound Q_pos join52 h51
  have ht52 : startTime R step52 ≤ t := by
    rw [start_eq_stop join52.1]
    exact (lt_of_not_ge hstop51).le
  by_cases hstop52 : t ≤ stopTime R step52
  · exact global_step_range S_pos K_pos R_pos Q_pos sigma_mem cert52 hud hu52 t ⟨ht52,hstop52⟩
  have h52 := global_step_endpoint S_pos K_pos R_pos Q_pos sigma_mem cert52 hud hu52
  have hu53 := join_bound Q_pos join53 h52
  have ht53 : startTime R step53 ≤ t := by
    rw [start_eq_stop join53.1]
    exact (lt_of_not_ge hstop52).le
  by_cases hstop53 : t ≤ stopTime R step53
  · exact global_step_range S_pos K_pos R_pos Q_pos sigma_mem cert53 hud hu53 t ⟨ht53,hstop53⟩
  have h53 := global_step_endpoint S_pos K_pos R_pos Q_pos sigma_mem cert53 hud hu53
  have hu54 := join_bound Q_pos join54 h53
  have ht54 : startTime R step54 ≤ t := by
    rw [start_eq_stop join54.1]
    exact (lt_of_not_ge hstop53).le
  by_cases hstop54 : t ≤ stopTime R step54
  · exact global_step_range S_pos K_pos R_pos Q_pos sigma_mem cert54 hud hu54 t ⟨ht54,hstop54⟩
  have h54 := global_step_endpoint S_pos K_pos R_pos Q_pos sigma_mem cert54 hud hu54
  have hu55 := join_bound Q_pos join55 h54
  have ht55 : startTime R step55 ≤ t := by
    rw [start_eq_stop join55.1]
    exact (lt_of_not_ge hstop54).le
  by_cases hstop55 : t ≤ stopTime R step55
  · exact global_step_range S_pos K_pos R_pos Q_pos sigma_mem cert55 hud hu55 t ⟨ht55,hstop55⟩
  have h55 := global_step_endpoint S_pos K_pos R_pos Q_pos sigma_mem cert55 hud hu55
  have hu56 := join_bound Q_pos join56 h55
  have ht56 : startTime R step56 ≤ t := by
    rw [start_eq_stop join56.1]
    exact (lt_of_not_ge hstop55).le
  by_cases hstop56 : t ≤ stopTime R step56
  · exact global_step_range S_pos K_pos R_pos Q_pos sigma_mem cert56 hud hu56 t ⟨ht56,hstop56⟩
  have h56 := global_step_endpoint S_pos K_pos R_pos Q_pos sigma_mem cert56 hud hu56
  have hu57 := join_bound Q_pos join57 h56
  have ht57 : startTime R step57 ≤ t := by
    rw [start_eq_stop join57.1]
    exact (lt_of_not_ge hstop56).le
  by_cases hstop57 : t ≤ stopTime R step57
  · exact global_step_range S_pos K_pos R_pos Q_pos sigma_mem cert57 hud hu57 t ⟨ht57,hstop57⟩
  have h57 := global_step_endpoint S_pos K_pos R_pos Q_pos sigma_mem cert57 hud hu57
  have hu58 := join_bound Q_pos join58 h57
  have ht58 : startTime R step58 ≤ t := by
    rw [start_eq_stop join58.1]
    exact (lt_of_not_ge hstop57).le
  by_cases hstop58 : t ≤ stopTime R step58
  · exact global_step_range S_pos K_pos R_pos Q_pos sigma_mem cert58 hud hu58 t ⟨ht58,hstop58⟩
  have h58 := global_step_endpoint S_pos K_pos R_pos Q_pos sigma_mem cert58 hud hu58
  have hu59 := join_bound Q_pos join59 h58
  have ht59 : startTime R step59 ≤ t := by
    rw [start_eq_stop join59.1]
    exact (lt_of_not_ge hstop58).le
  by_cases hstop59 : t ≤ stopTime R step59
  · exact global_step_range S_pos K_pos R_pos Q_pos sigma_mem cert59 hud hu59 t ⟨ht59,hstop59⟩
  have h59 := global_step_endpoint S_pos K_pos R_pos Q_pos sigma_mem cert59 hud hu59
  have hu60 := join_bound Q_pos join60 h59
  have ht60 : startTime R step60 ≤ t := by
    rw [start_eq_stop join60.1]
    exact (lt_of_not_ge hstop59).le
  by_cases hstop60 : t ≤ stopTime R step60
  · exact global_step_range S_pos K_pos R_pos Q_pos sigma_mem cert60 hud hu60 t ⟨ht60,hstop60⟩
  have h60 := global_step_endpoint S_pos K_pos R_pos Q_pos sigma_mem cert60 hud hu60
  have hu61 := join_bound Q_pos join61 h60
  have ht61 : startTime R step61 ≤ t := by
    rw [start_eq_stop join61.1]
    exact (lt_of_not_ge hstop60).le
  by_cases hstop61 : t ≤ stopTime R step61
  · exact global_step_range S_pos K_pos R_pos Q_pos sigma_mem cert61 hud hu61 t ⟨ht61,hstop61⟩
  have h61 := global_step_endpoint S_pos K_pos R_pos Q_pos sigma_mem cert61 hud hu61
  have hu62 := join_bound Q_pos join62 h61
  have ht62 : startTime R step62 ≤ t := by
    rw [start_eq_stop join62.1]
    exact (lt_of_not_ge hstop61).le
  by_cases hstop62 : t ≤ stopTime R step62
  · exact global_step_range S_pos K_pos R_pos Q_pos sigma_mem cert62 hud hu62 t ⟨ht62,hstop62⟩
  have h62 := global_step_endpoint S_pos K_pos R_pos Q_pos sigma_mem cert62 hud hu62
  have hu63 := join_bound Q_pos join63 h62
  have ht63 : startTime R step63 ≤ t := by
    rw [start_eq_stop join63.1]
    exact (lt_of_not_ge hstop62).le
  exact global_step_range S_pos K_pos R_pos Q_pos sigma_mem cert63 hud hu63 t ⟨ht63,ht.2⟩
theorem range_64 {u : ℝ → ℝ} (hud : ∀ t ∈ Icc (0:ℝ) (9/100), HasDerivWithinAt u
    (globalField (SN/S) (KN/K) t (u t)) (Icc 0 (9/100)) t)
    (hu : u (startTime R step64) ∈ Icc ((head step64.lo:ℝ)/Q) ((head step64.hi:ℝ)/Q)) :
    ∀ t ∈ Icc (startTime R step64) (stopTime R step79), u t ∈ Icc (0:ℝ) (999/1000) := by
  intro t ht
  have ht64 := ht.1
  by_cases hstop64 : t ≤ stopTime R step64
  · exact global_step_range S_pos K_pos R_pos Q_pos sigma_mem cert64 hud hu t ⟨ht64,hstop64⟩
  have h64 := global_step_endpoint S_pos K_pos R_pos Q_pos sigma_mem cert64 hud hu
  have hu65 := join_bound Q_pos join65 h64
  have ht65 : startTime R step65 ≤ t := by
    rw [start_eq_stop join65.1]
    exact (lt_of_not_ge hstop64).le
  by_cases hstop65 : t ≤ stopTime R step65
  · exact global_step_range S_pos K_pos R_pos Q_pos sigma_mem cert65 hud hu65 t ⟨ht65,hstop65⟩
  have h65 := global_step_endpoint S_pos K_pos R_pos Q_pos sigma_mem cert65 hud hu65
  have hu66 := join_bound Q_pos join66 h65
  have ht66 : startTime R step66 ≤ t := by
    rw [start_eq_stop join66.1]
    exact (lt_of_not_ge hstop65).le
  by_cases hstop66 : t ≤ stopTime R step66
  · exact global_step_range S_pos K_pos R_pos Q_pos sigma_mem cert66 hud hu66 t ⟨ht66,hstop66⟩
  have h66 := global_step_endpoint S_pos K_pos R_pos Q_pos sigma_mem cert66 hud hu66
  have hu67 := join_bound Q_pos join67 h66
  have ht67 : startTime R step67 ≤ t := by
    rw [start_eq_stop join67.1]
    exact (lt_of_not_ge hstop66).le
  by_cases hstop67 : t ≤ stopTime R step67
  · exact global_step_range S_pos K_pos R_pos Q_pos sigma_mem cert67 hud hu67 t ⟨ht67,hstop67⟩
  have h67 := global_step_endpoint S_pos K_pos R_pos Q_pos sigma_mem cert67 hud hu67
  have hu68 := join_bound Q_pos join68 h67
  have ht68 : startTime R step68 ≤ t := by
    rw [start_eq_stop join68.1]
    exact (lt_of_not_ge hstop67).le
  by_cases hstop68 : t ≤ stopTime R step68
  · exact global_step_range S_pos K_pos R_pos Q_pos sigma_mem cert68 hud hu68 t ⟨ht68,hstop68⟩
  have h68 := global_step_endpoint S_pos K_pos R_pos Q_pos sigma_mem cert68 hud hu68
  have hu69 := join_bound Q_pos join69 h68
  have ht69 : startTime R step69 ≤ t := by
    rw [start_eq_stop join69.1]
    exact (lt_of_not_ge hstop68).le
  by_cases hstop69 : t ≤ stopTime R step69
  · exact global_step_range S_pos K_pos R_pos Q_pos sigma_mem cert69 hud hu69 t ⟨ht69,hstop69⟩
  have h69 := global_step_endpoint S_pos K_pos R_pos Q_pos sigma_mem cert69 hud hu69
  have hu70 := join_bound Q_pos join70 h69
  have ht70 : startTime R step70 ≤ t := by
    rw [start_eq_stop join70.1]
    exact (lt_of_not_ge hstop69).le
  by_cases hstop70 : t ≤ stopTime R step70
  · exact global_step_range S_pos K_pos R_pos Q_pos sigma_mem cert70 hud hu70 t ⟨ht70,hstop70⟩
  have h70 := global_step_endpoint S_pos K_pos R_pos Q_pos sigma_mem cert70 hud hu70
  have hu71 := join_bound Q_pos join71 h70
  have ht71 : startTime R step71 ≤ t := by
    rw [start_eq_stop join71.1]
    exact (lt_of_not_ge hstop70).le
  by_cases hstop71 : t ≤ stopTime R step71
  · exact global_step_range S_pos K_pos R_pos Q_pos sigma_mem cert71 hud hu71 t ⟨ht71,hstop71⟩
  have h71 := global_step_endpoint S_pos K_pos R_pos Q_pos sigma_mem cert71 hud hu71
  have hu72 := join_bound Q_pos join72 h71
  have ht72 : startTime R step72 ≤ t := by
    rw [start_eq_stop join72.1]
    exact (lt_of_not_ge hstop71).le
  by_cases hstop72 : t ≤ stopTime R step72
  · exact global_step_range S_pos K_pos R_pos Q_pos sigma_mem cert72 hud hu72 t ⟨ht72,hstop72⟩
  have h72 := global_step_endpoint S_pos K_pos R_pos Q_pos sigma_mem cert72 hud hu72
  have hu73 := join_bound Q_pos join73 h72
  have ht73 : startTime R step73 ≤ t := by
    rw [start_eq_stop join73.1]
    exact (lt_of_not_ge hstop72).le
  by_cases hstop73 : t ≤ stopTime R step73
  · exact global_step_range S_pos K_pos R_pos Q_pos sigma_mem cert73 hud hu73 t ⟨ht73,hstop73⟩
  have h73 := global_step_endpoint S_pos K_pos R_pos Q_pos sigma_mem cert73 hud hu73
  have hu74 := join_bound Q_pos join74 h73
  have ht74 : startTime R step74 ≤ t := by
    rw [start_eq_stop join74.1]
    exact (lt_of_not_ge hstop73).le
  by_cases hstop74 : t ≤ stopTime R step74
  · exact global_step_range S_pos K_pos R_pos Q_pos sigma_mem cert74 hud hu74 t ⟨ht74,hstop74⟩
  have h74 := global_step_endpoint S_pos K_pos R_pos Q_pos sigma_mem cert74 hud hu74
  have hu75 := join_bound Q_pos join75 h74
  have ht75 : startTime R step75 ≤ t := by
    rw [start_eq_stop join75.1]
    exact (lt_of_not_ge hstop74).le
  by_cases hstop75 : t ≤ stopTime R step75
  · exact global_step_range S_pos K_pos R_pos Q_pos sigma_mem cert75 hud hu75 t ⟨ht75,hstop75⟩
  have h75 := global_step_endpoint S_pos K_pos R_pos Q_pos sigma_mem cert75 hud hu75
  have hu76 := join_bound Q_pos join76 h75
  have ht76 : startTime R step76 ≤ t := by
    rw [start_eq_stop join76.1]
    exact (lt_of_not_ge hstop75).le
  by_cases hstop76 : t ≤ stopTime R step76
  · exact global_step_range S_pos K_pos R_pos Q_pos sigma_mem cert76 hud hu76 t ⟨ht76,hstop76⟩
  have h76 := global_step_endpoint S_pos K_pos R_pos Q_pos sigma_mem cert76 hud hu76
  have hu77 := join_bound Q_pos join77 h76
  have ht77 : startTime R step77 ≤ t := by
    rw [start_eq_stop join77.1]
    exact (lt_of_not_ge hstop76).le
  by_cases hstop77 : t ≤ stopTime R step77
  · exact global_step_range S_pos K_pos R_pos Q_pos sigma_mem cert77 hud hu77 t ⟨ht77,hstop77⟩
  have h77 := global_step_endpoint S_pos K_pos R_pos Q_pos sigma_mem cert77 hud hu77
  have hu78 := join_bound Q_pos join78 h77
  have ht78 : startTime R step78 ≤ t := by
    rw [start_eq_stop join78.1]
    exact (lt_of_not_ge hstop77).le
  by_cases hstop78 : t ≤ stopTime R step78
  · exact global_step_range S_pos K_pos R_pos Q_pos sigma_mem cert78 hud hu78 t ⟨ht78,hstop78⟩
  have h78 := global_step_endpoint S_pos K_pos R_pos Q_pos sigma_mem cert78 hud hu78
  have hu79 := join_bound Q_pos join79 h78
  have ht79 : startTime R step79 ≤ t := by
    rw [start_eq_stop join79.1]
    exact (lt_of_not_ge hstop78).le
  exact global_step_range S_pos K_pos R_pos Q_pos sigma_mem cert79 hud hu79 t ⟨ht79,ht.2⟩
theorem range_80 {u : ℝ → ℝ} (hud : ∀ t ∈ Icc (0:ℝ) (9/100), HasDerivWithinAt u
    (globalField (SN/S) (KN/K) t (u t)) (Icc 0 (9/100)) t)
    (hu : u (startTime R step80) ∈ Icc ((head step80.lo:ℝ)/Q) ((head step80.hi:ℝ)/Q)) :
    ∀ t ∈ Icc (startTime R step80) (stopTime R step95), u t ∈ Icc (0:ℝ) (999/1000) := by
  intro t ht
  have ht80 := ht.1
  by_cases hstop80 : t ≤ stopTime R step80
  · exact global_step_range S_pos K_pos R_pos Q_pos sigma_mem cert80 hud hu t ⟨ht80,hstop80⟩
  have h80 := global_step_endpoint S_pos K_pos R_pos Q_pos sigma_mem cert80 hud hu
  have hu81 := join_bound Q_pos join81 h80
  have ht81 : startTime R step81 ≤ t := by
    rw [start_eq_stop join81.1]
    exact (lt_of_not_ge hstop80).le
  by_cases hstop81 : t ≤ stopTime R step81
  · exact global_step_range S_pos K_pos R_pos Q_pos sigma_mem cert81 hud hu81 t ⟨ht81,hstop81⟩
  have h81 := global_step_endpoint S_pos K_pos R_pos Q_pos sigma_mem cert81 hud hu81
  have hu82 := join_bound Q_pos join82 h81
  have ht82 : startTime R step82 ≤ t := by
    rw [start_eq_stop join82.1]
    exact (lt_of_not_ge hstop81).le
  by_cases hstop82 : t ≤ stopTime R step82
  · exact global_step_range S_pos K_pos R_pos Q_pos sigma_mem cert82 hud hu82 t ⟨ht82,hstop82⟩
  have h82 := global_step_endpoint S_pos K_pos R_pos Q_pos sigma_mem cert82 hud hu82
  have hu83 := join_bound Q_pos join83 h82
  have ht83 : startTime R step83 ≤ t := by
    rw [start_eq_stop join83.1]
    exact (lt_of_not_ge hstop82).le
  by_cases hstop83 : t ≤ stopTime R step83
  · exact global_step_range S_pos K_pos R_pos Q_pos sigma_mem cert83 hud hu83 t ⟨ht83,hstop83⟩
  have h83 := global_step_endpoint S_pos K_pos R_pos Q_pos sigma_mem cert83 hud hu83
  have hu84 := join_bound Q_pos join84 h83
  have ht84 : startTime R step84 ≤ t := by
    rw [start_eq_stop join84.1]
    exact (lt_of_not_ge hstop83).le
  by_cases hstop84 : t ≤ stopTime R step84
  · exact global_step_range S_pos K_pos R_pos Q_pos sigma_mem cert84 hud hu84 t ⟨ht84,hstop84⟩
  have h84 := global_step_endpoint S_pos K_pos R_pos Q_pos sigma_mem cert84 hud hu84
  have hu85 := join_bound Q_pos join85 h84
  have ht85 : startTime R step85 ≤ t := by
    rw [start_eq_stop join85.1]
    exact (lt_of_not_ge hstop84).le
  by_cases hstop85 : t ≤ stopTime R step85
  · exact global_step_range S_pos K_pos R_pos Q_pos sigma_mem cert85 hud hu85 t ⟨ht85,hstop85⟩
  have h85 := global_step_endpoint S_pos K_pos R_pos Q_pos sigma_mem cert85 hud hu85
  have hu86 := join_bound Q_pos join86 h85
  have ht86 : startTime R step86 ≤ t := by
    rw [start_eq_stop join86.1]
    exact (lt_of_not_ge hstop85).le
  by_cases hstop86 : t ≤ stopTime R step86
  · exact global_step_range S_pos K_pos R_pos Q_pos sigma_mem cert86 hud hu86 t ⟨ht86,hstop86⟩
  have h86 := global_step_endpoint S_pos K_pos R_pos Q_pos sigma_mem cert86 hud hu86
  have hu87 := join_bound Q_pos join87 h86
  have ht87 : startTime R step87 ≤ t := by
    rw [start_eq_stop join87.1]
    exact (lt_of_not_ge hstop86).le
  by_cases hstop87 : t ≤ stopTime R step87
  · exact global_step_range S_pos K_pos R_pos Q_pos sigma_mem cert87 hud hu87 t ⟨ht87,hstop87⟩
  have h87 := global_step_endpoint S_pos K_pos R_pos Q_pos sigma_mem cert87 hud hu87
  have hu88 := join_bound Q_pos join88 h87
  have ht88 : startTime R step88 ≤ t := by
    rw [start_eq_stop join88.1]
    exact (lt_of_not_ge hstop87).le
  by_cases hstop88 : t ≤ stopTime R step88
  · exact global_step_range S_pos K_pos R_pos Q_pos sigma_mem cert88 hud hu88 t ⟨ht88,hstop88⟩
  have h88 := global_step_endpoint S_pos K_pos R_pos Q_pos sigma_mem cert88 hud hu88
  have hu89 := join_bound Q_pos join89 h88
  have ht89 : startTime R step89 ≤ t := by
    rw [start_eq_stop join89.1]
    exact (lt_of_not_ge hstop88).le
  by_cases hstop89 : t ≤ stopTime R step89
  · exact global_step_range S_pos K_pos R_pos Q_pos sigma_mem cert89 hud hu89 t ⟨ht89,hstop89⟩
  have h89 := global_step_endpoint S_pos K_pos R_pos Q_pos sigma_mem cert89 hud hu89
  have hu90 := join_bound Q_pos join90 h89
  have ht90 : startTime R step90 ≤ t := by
    rw [start_eq_stop join90.1]
    exact (lt_of_not_ge hstop89).le
  by_cases hstop90 : t ≤ stopTime R step90
  · exact global_step_range S_pos K_pos R_pos Q_pos sigma_mem cert90 hud hu90 t ⟨ht90,hstop90⟩
  have h90 := global_step_endpoint S_pos K_pos R_pos Q_pos sigma_mem cert90 hud hu90
  have hu91 := join_bound Q_pos join91 h90
  have ht91 : startTime R step91 ≤ t := by
    rw [start_eq_stop join91.1]
    exact (lt_of_not_ge hstop90).le
  by_cases hstop91 : t ≤ stopTime R step91
  · exact global_step_range S_pos K_pos R_pos Q_pos sigma_mem cert91 hud hu91 t ⟨ht91,hstop91⟩
  have h91 := global_step_endpoint S_pos K_pos R_pos Q_pos sigma_mem cert91 hud hu91
  have hu92 := join_bound Q_pos join92 h91
  have ht92 : startTime R step92 ≤ t := by
    rw [start_eq_stop join92.1]
    exact (lt_of_not_ge hstop91).le
  by_cases hstop92 : t ≤ stopTime R step92
  · exact global_step_range S_pos K_pos R_pos Q_pos sigma_mem cert92 hud hu92 t ⟨ht92,hstop92⟩
  have h92 := global_step_endpoint S_pos K_pos R_pos Q_pos sigma_mem cert92 hud hu92
  have hu93 := join_bound Q_pos join93 h92
  have ht93 : startTime R step93 ≤ t := by
    rw [start_eq_stop join93.1]
    exact (lt_of_not_ge hstop92).le
  by_cases hstop93 : t ≤ stopTime R step93
  · exact global_step_range S_pos K_pos R_pos Q_pos sigma_mem cert93 hud hu93 t ⟨ht93,hstop93⟩
  have h93 := global_step_endpoint S_pos K_pos R_pos Q_pos sigma_mem cert93 hud hu93
  have hu94 := join_bound Q_pos join94 h93
  have ht94 : startTime R step94 ≤ t := by
    rw [start_eq_stop join94.1]
    exact (lt_of_not_ge hstop93).le
  by_cases hstop94 : t ≤ stopTime R step94
  · exact global_step_range S_pos K_pos R_pos Q_pos sigma_mem cert94 hud hu94 t ⟨ht94,hstop94⟩
  have h94 := global_step_endpoint S_pos K_pos R_pos Q_pos sigma_mem cert94 hud hu94
  have hu95 := join_bound Q_pos join95 h94
  have ht95 : startTime R step95 ≤ t := by
    rw [start_eq_stop join95.1]
    exact (lt_of_not_ge hstop94).le
  exact global_step_range S_pos K_pos R_pos Q_pos sigma_mem cert95 hud hu95 t ⟨ht95,ht.2⟩
theorem range_96 {u : ℝ → ℝ} (hud : ∀ t ∈ Icc (0:ℝ) (9/100), HasDerivWithinAt u
    (globalField (SN/S) (KN/K) t (u t)) (Icc 0 (9/100)) t)
    (hu : u (startTime R step96) ∈ Icc ((head step96.lo:ℝ)/Q) ((head step96.hi:ℝ)/Q)) :
    ∀ t ∈ Icc (startTime R step96) (stopTime R step111), u t ∈ Icc (0:ℝ) (999/1000) := by
  intro t ht
  have ht96 := ht.1
  by_cases hstop96 : t ≤ stopTime R step96
  · exact global_step_range S_pos K_pos R_pos Q_pos sigma_mem cert96 hud hu t ⟨ht96,hstop96⟩
  have h96 := global_step_endpoint S_pos K_pos R_pos Q_pos sigma_mem cert96 hud hu
  have hu97 := join_bound Q_pos join97 h96
  have ht97 : startTime R step97 ≤ t := by
    rw [start_eq_stop join97.1]
    exact (lt_of_not_ge hstop96).le
  by_cases hstop97 : t ≤ stopTime R step97
  · exact global_step_range S_pos K_pos R_pos Q_pos sigma_mem cert97 hud hu97 t ⟨ht97,hstop97⟩
  have h97 := global_step_endpoint S_pos K_pos R_pos Q_pos sigma_mem cert97 hud hu97
  have hu98 := join_bound Q_pos join98 h97
  have ht98 : startTime R step98 ≤ t := by
    rw [start_eq_stop join98.1]
    exact (lt_of_not_ge hstop97).le
  by_cases hstop98 : t ≤ stopTime R step98
  · exact global_step_range S_pos K_pos R_pos Q_pos sigma_mem cert98 hud hu98 t ⟨ht98,hstop98⟩
  have h98 := global_step_endpoint S_pos K_pos R_pos Q_pos sigma_mem cert98 hud hu98
  have hu99 := join_bound Q_pos join99 h98
  have ht99 : startTime R step99 ≤ t := by
    rw [start_eq_stop join99.1]
    exact (lt_of_not_ge hstop98).le
  by_cases hstop99 : t ≤ stopTime R step99
  · exact global_step_range S_pos K_pos R_pos Q_pos sigma_mem cert99 hud hu99 t ⟨ht99,hstop99⟩
  have h99 := global_step_endpoint S_pos K_pos R_pos Q_pos sigma_mem cert99 hud hu99
  have hu100 := join_bound Q_pos join100 h99
  have ht100 : startTime R step100 ≤ t := by
    rw [start_eq_stop join100.1]
    exact (lt_of_not_ge hstop99).le
  by_cases hstop100 : t ≤ stopTime R step100
  · exact global_step_range S_pos K_pos R_pos Q_pos sigma_mem cert100 hud hu100 t ⟨ht100,hstop100⟩
  have h100 := global_step_endpoint S_pos K_pos R_pos Q_pos sigma_mem cert100 hud hu100
  have hu101 := join_bound Q_pos join101 h100
  have ht101 : startTime R step101 ≤ t := by
    rw [start_eq_stop join101.1]
    exact (lt_of_not_ge hstop100).le
  by_cases hstop101 : t ≤ stopTime R step101
  · exact global_step_range S_pos K_pos R_pos Q_pos sigma_mem cert101 hud hu101 t ⟨ht101,hstop101⟩
  have h101 := global_step_endpoint S_pos K_pos R_pos Q_pos sigma_mem cert101 hud hu101
  have hu102 := join_bound Q_pos join102 h101
  have ht102 : startTime R step102 ≤ t := by
    rw [start_eq_stop join102.1]
    exact (lt_of_not_ge hstop101).le
  by_cases hstop102 : t ≤ stopTime R step102
  · exact global_step_range S_pos K_pos R_pos Q_pos sigma_mem cert102 hud hu102 t ⟨ht102,hstop102⟩
  have h102 := global_step_endpoint S_pos K_pos R_pos Q_pos sigma_mem cert102 hud hu102
  have hu103 := join_bound Q_pos join103 h102
  have ht103 : startTime R step103 ≤ t := by
    rw [start_eq_stop join103.1]
    exact (lt_of_not_ge hstop102).le
  by_cases hstop103 : t ≤ stopTime R step103
  · exact global_step_range S_pos K_pos R_pos Q_pos sigma_mem cert103 hud hu103 t ⟨ht103,hstop103⟩
  have h103 := global_step_endpoint S_pos K_pos R_pos Q_pos sigma_mem cert103 hud hu103
  have hu104 := join_bound Q_pos join104 h103
  have ht104 : startTime R step104 ≤ t := by
    rw [start_eq_stop join104.1]
    exact (lt_of_not_ge hstop103).le
  by_cases hstop104 : t ≤ stopTime R step104
  · exact global_step_range S_pos K_pos R_pos Q_pos sigma_mem cert104 hud hu104 t ⟨ht104,hstop104⟩
  have h104 := global_step_endpoint S_pos K_pos R_pos Q_pos sigma_mem cert104 hud hu104
  have hu105 := join_bound Q_pos join105 h104
  have ht105 : startTime R step105 ≤ t := by
    rw [start_eq_stop join105.1]
    exact (lt_of_not_ge hstop104).le
  by_cases hstop105 : t ≤ stopTime R step105
  · exact global_step_range S_pos K_pos R_pos Q_pos sigma_mem cert105 hud hu105 t ⟨ht105,hstop105⟩
  have h105 := global_step_endpoint S_pos K_pos R_pos Q_pos sigma_mem cert105 hud hu105
  have hu106 := join_bound Q_pos join106 h105
  have ht106 : startTime R step106 ≤ t := by
    rw [start_eq_stop join106.1]
    exact (lt_of_not_ge hstop105).le
  by_cases hstop106 : t ≤ stopTime R step106
  · exact global_step_range S_pos K_pos R_pos Q_pos sigma_mem cert106 hud hu106 t ⟨ht106,hstop106⟩
  have h106 := global_step_endpoint S_pos K_pos R_pos Q_pos sigma_mem cert106 hud hu106
  have hu107 := join_bound Q_pos join107 h106
  have ht107 : startTime R step107 ≤ t := by
    rw [start_eq_stop join107.1]
    exact (lt_of_not_ge hstop106).le
  by_cases hstop107 : t ≤ stopTime R step107
  · exact global_step_range S_pos K_pos R_pos Q_pos sigma_mem cert107 hud hu107 t ⟨ht107,hstop107⟩
  have h107 := global_step_endpoint S_pos K_pos R_pos Q_pos sigma_mem cert107 hud hu107
  have hu108 := join_bound Q_pos join108 h107
  have ht108 : startTime R step108 ≤ t := by
    rw [start_eq_stop join108.1]
    exact (lt_of_not_ge hstop107).le
  by_cases hstop108 : t ≤ stopTime R step108
  · exact global_step_range S_pos K_pos R_pos Q_pos sigma_mem cert108 hud hu108 t ⟨ht108,hstop108⟩
  have h108 := global_step_endpoint S_pos K_pos R_pos Q_pos sigma_mem cert108 hud hu108
  have hu109 := join_bound Q_pos join109 h108
  have ht109 : startTime R step109 ≤ t := by
    rw [start_eq_stop join109.1]
    exact (lt_of_not_ge hstop108).le
  by_cases hstop109 : t ≤ stopTime R step109
  · exact global_step_range S_pos K_pos R_pos Q_pos sigma_mem cert109 hud hu109 t ⟨ht109,hstop109⟩
  have h109 := global_step_endpoint S_pos K_pos R_pos Q_pos sigma_mem cert109 hud hu109
  have hu110 := join_bound Q_pos join110 h109
  have ht110 : startTime R step110 ≤ t := by
    rw [start_eq_stop join110.1]
    exact (lt_of_not_ge hstop109).le
  by_cases hstop110 : t ≤ stopTime R step110
  · exact global_step_range S_pos K_pos R_pos Q_pos sigma_mem cert110 hud hu110 t ⟨ht110,hstop110⟩
  have h110 := global_step_endpoint S_pos K_pos R_pos Q_pos sigma_mem cert110 hud hu110
  have hu111 := join_bound Q_pos join111 h110
  have ht111 : startTime R step111 ≤ t := by
    rw [start_eq_stop join111.1]
    exact (lt_of_not_ge hstop110).le
  exact global_step_range S_pos K_pos R_pos Q_pos sigma_mem cert111 hud hu111 t ⟨ht111,ht.2⟩
theorem range_112 {u : ℝ → ℝ} (hud : ∀ t ∈ Icc (0:ℝ) (9/100), HasDerivWithinAt u
    (globalField (SN/S) (KN/K) t (u t)) (Icc 0 (9/100)) t)
    (hu : u (startTime R step112) ∈ Icc ((head step112.lo:ℝ)/Q) ((head step112.hi:ℝ)/Q)) :
    ∀ t ∈ Icc (startTime R step112) (stopTime R step127), u t ∈ Icc (0:ℝ) (999/1000) := by
  intro t ht
  have ht112 := ht.1
  by_cases hstop112 : t ≤ stopTime R step112
  · exact global_step_range S_pos K_pos R_pos Q_pos sigma_mem cert112 hud hu t ⟨ht112,hstop112⟩
  have h112 := global_step_endpoint S_pos K_pos R_pos Q_pos sigma_mem cert112 hud hu
  have hu113 := join_bound Q_pos join113 h112
  have ht113 : startTime R step113 ≤ t := by
    rw [start_eq_stop join113.1]
    exact (lt_of_not_ge hstop112).le
  by_cases hstop113 : t ≤ stopTime R step113
  · exact global_step_range S_pos K_pos R_pos Q_pos sigma_mem cert113 hud hu113 t ⟨ht113,hstop113⟩
  have h113 := global_step_endpoint S_pos K_pos R_pos Q_pos sigma_mem cert113 hud hu113
  have hu114 := join_bound Q_pos join114 h113
  have ht114 : startTime R step114 ≤ t := by
    rw [start_eq_stop join114.1]
    exact (lt_of_not_ge hstop113).le
  by_cases hstop114 : t ≤ stopTime R step114
  · exact global_step_range S_pos K_pos R_pos Q_pos sigma_mem cert114 hud hu114 t ⟨ht114,hstop114⟩
  have h114 := global_step_endpoint S_pos K_pos R_pos Q_pos sigma_mem cert114 hud hu114
  have hu115 := join_bound Q_pos join115 h114
  have ht115 : startTime R step115 ≤ t := by
    rw [start_eq_stop join115.1]
    exact (lt_of_not_ge hstop114).le
  by_cases hstop115 : t ≤ stopTime R step115
  · exact global_step_range S_pos K_pos R_pos Q_pos sigma_mem cert115 hud hu115 t ⟨ht115,hstop115⟩
  have h115 := global_step_endpoint S_pos K_pos R_pos Q_pos sigma_mem cert115 hud hu115
  have hu116 := join_bound Q_pos join116 h115
  have ht116 : startTime R step116 ≤ t := by
    rw [start_eq_stop join116.1]
    exact (lt_of_not_ge hstop115).le
  by_cases hstop116 : t ≤ stopTime R step116
  · exact global_step_range S_pos K_pos R_pos Q_pos sigma_mem cert116 hud hu116 t ⟨ht116,hstop116⟩
  have h116 := global_step_endpoint S_pos K_pos R_pos Q_pos sigma_mem cert116 hud hu116
  have hu117 := join_bound Q_pos join117 h116
  have ht117 : startTime R step117 ≤ t := by
    rw [start_eq_stop join117.1]
    exact (lt_of_not_ge hstop116).le
  by_cases hstop117 : t ≤ stopTime R step117
  · exact global_step_range S_pos K_pos R_pos Q_pos sigma_mem cert117 hud hu117 t ⟨ht117,hstop117⟩
  have h117 := global_step_endpoint S_pos K_pos R_pos Q_pos sigma_mem cert117 hud hu117
  have hu118 := join_bound Q_pos join118 h117
  have ht118 : startTime R step118 ≤ t := by
    rw [start_eq_stop join118.1]
    exact (lt_of_not_ge hstop117).le
  by_cases hstop118 : t ≤ stopTime R step118
  · exact global_step_range S_pos K_pos R_pos Q_pos sigma_mem cert118 hud hu118 t ⟨ht118,hstop118⟩
  have h118 := global_step_endpoint S_pos K_pos R_pos Q_pos sigma_mem cert118 hud hu118
  have hu119 := join_bound Q_pos join119 h118
  have ht119 : startTime R step119 ≤ t := by
    rw [start_eq_stop join119.1]
    exact (lt_of_not_ge hstop118).le
  by_cases hstop119 : t ≤ stopTime R step119
  · exact global_step_range S_pos K_pos R_pos Q_pos sigma_mem cert119 hud hu119 t ⟨ht119,hstop119⟩
  have h119 := global_step_endpoint S_pos K_pos R_pos Q_pos sigma_mem cert119 hud hu119
  have hu120 := join_bound Q_pos join120 h119
  have ht120 : startTime R step120 ≤ t := by
    rw [start_eq_stop join120.1]
    exact (lt_of_not_ge hstop119).le
  by_cases hstop120 : t ≤ stopTime R step120
  · exact global_step_range S_pos K_pos R_pos Q_pos sigma_mem cert120 hud hu120 t ⟨ht120,hstop120⟩
  have h120 := global_step_endpoint S_pos K_pos R_pos Q_pos sigma_mem cert120 hud hu120
  have hu121 := join_bound Q_pos join121 h120
  have ht121 : startTime R step121 ≤ t := by
    rw [start_eq_stop join121.1]
    exact (lt_of_not_ge hstop120).le
  by_cases hstop121 : t ≤ stopTime R step121
  · exact global_step_range S_pos K_pos R_pos Q_pos sigma_mem cert121 hud hu121 t ⟨ht121,hstop121⟩
  have h121 := global_step_endpoint S_pos K_pos R_pos Q_pos sigma_mem cert121 hud hu121
  have hu122 := join_bound Q_pos join122 h121
  have ht122 : startTime R step122 ≤ t := by
    rw [start_eq_stop join122.1]
    exact (lt_of_not_ge hstop121).le
  by_cases hstop122 : t ≤ stopTime R step122
  · exact global_step_range S_pos K_pos R_pos Q_pos sigma_mem cert122 hud hu122 t ⟨ht122,hstop122⟩
  have h122 := global_step_endpoint S_pos K_pos R_pos Q_pos sigma_mem cert122 hud hu122
  have hu123 := join_bound Q_pos join123 h122
  have ht123 : startTime R step123 ≤ t := by
    rw [start_eq_stop join123.1]
    exact (lt_of_not_ge hstop122).le
  by_cases hstop123 : t ≤ stopTime R step123
  · exact global_step_range S_pos K_pos R_pos Q_pos sigma_mem cert123 hud hu123 t ⟨ht123,hstop123⟩
  have h123 := global_step_endpoint S_pos K_pos R_pos Q_pos sigma_mem cert123 hud hu123
  have hu124 := join_bound Q_pos join124 h123
  have ht124 : startTime R step124 ≤ t := by
    rw [start_eq_stop join124.1]
    exact (lt_of_not_ge hstop123).le
  by_cases hstop124 : t ≤ stopTime R step124
  · exact global_step_range S_pos K_pos R_pos Q_pos sigma_mem cert124 hud hu124 t ⟨ht124,hstop124⟩
  have h124 := global_step_endpoint S_pos K_pos R_pos Q_pos sigma_mem cert124 hud hu124
  have hu125 := join_bound Q_pos join125 h124
  have ht125 : startTime R step125 ≤ t := by
    rw [start_eq_stop join125.1]
    exact (lt_of_not_ge hstop124).le
  by_cases hstop125 : t ≤ stopTime R step125
  · exact global_step_range S_pos K_pos R_pos Q_pos sigma_mem cert125 hud hu125 t ⟨ht125,hstop125⟩
  have h125 := global_step_endpoint S_pos K_pos R_pos Q_pos sigma_mem cert125 hud hu125
  have hu126 := join_bound Q_pos join126 h125
  have ht126 : startTime R step126 ≤ t := by
    rw [start_eq_stop join126.1]
    exact (lt_of_not_ge hstop125).le
  by_cases hstop126 : t ≤ stopTime R step126
  · exact global_step_range S_pos K_pos R_pos Q_pos sigma_mem cert126 hud hu126 t ⟨ht126,hstop126⟩
  have h126 := global_step_endpoint S_pos K_pos R_pos Q_pos sigma_mem cert126 hud hu126
  have hu127 := join_bound Q_pos join127 h126
  have ht127 : startTime R step127 ≤ t := by
    rw [start_eq_stop join127.1]
    exact (lt_of_not_ge hstop126).le
  exact global_step_range S_pos K_pos R_pos Q_pos sigma_mem cert127 hud hu127 t ⟨ht127,ht.2⟩
theorem range_128 {u : ℝ → ℝ} (hud : ∀ t ∈ Icc (0:ℝ) (9/100), HasDerivWithinAt u
    (globalField (SN/S) (KN/K) t (u t)) (Icc 0 (9/100)) t)
    (hu : u (startTime R step128) ∈ Icc ((head step128.lo:ℝ)/Q) ((head step128.hi:ℝ)/Q)) :
    ∀ t ∈ Icc (startTime R step128) (stopTime R step143), u t ∈ Icc (0:ℝ) (999/1000) := by
  intro t ht
  have ht128 := ht.1
  by_cases hstop128 : t ≤ stopTime R step128
  · exact global_step_range S_pos K_pos R_pos Q_pos sigma_mem cert128 hud hu t ⟨ht128,hstop128⟩
  have h128 := global_step_endpoint S_pos K_pos R_pos Q_pos sigma_mem cert128 hud hu
  have hu129 := join_bound Q_pos join129 h128
  have ht129 : startTime R step129 ≤ t := by
    rw [start_eq_stop join129.1]
    exact (lt_of_not_ge hstop128).le
  by_cases hstop129 : t ≤ stopTime R step129
  · exact global_step_range S_pos K_pos R_pos Q_pos sigma_mem cert129 hud hu129 t ⟨ht129,hstop129⟩
  have h129 := global_step_endpoint S_pos K_pos R_pos Q_pos sigma_mem cert129 hud hu129
  have hu130 := join_bound Q_pos join130 h129
  have ht130 : startTime R step130 ≤ t := by
    rw [start_eq_stop join130.1]
    exact (lt_of_not_ge hstop129).le
  by_cases hstop130 : t ≤ stopTime R step130
  · exact global_step_range S_pos K_pos R_pos Q_pos sigma_mem cert130 hud hu130 t ⟨ht130,hstop130⟩
  have h130 := global_step_endpoint S_pos K_pos R_pos Q_pos sigma_mem cert130 hud hu130
  have hu131 := join_bound Q_pos join131 h130
  have ht131 : startTime R step131 ≤ t := by
    rw [start_eq_stop join131.1]
    exact (lt_of_not_ge hstop130).le
  by_cases hstop131 : t ≤ stopTime R step131
  · exact global_step_range S_pos K_pos R_pos Q_pos sigma_mem cert131 hud hu131 t ⟨ht131,hstop131⟩
  have h131 := global_step_endpoint S_pos K_pos R_pos Q_pos sigma_mem cert131 hud hu131
  have hu132 := join_bound Q_pos join132 h131
  have ht132 : startTime R step132 ≤ t := by
    rw [start_eq_stop join132.1]
    exact (lt_of_not_ge hstop131).le
  by_cases hstop132 : t ≤ stopTime R step132
  · exact global_step_range S_pos K_pos R_pos Q_pos sigma_mem cert132 hud hu132 t ⟨ht132,hstop132⟩
  have h132 := global_step_endpoint S_pos K_pos R_pos Q_pos sigma_mem cert132 hud hu132
  have hu133 := join_bound Q_pos join133 h132
  have ht133 : startTime R step133 ≤ t := by
    rw [start_eq_stop join133.1]
    exact (lt_of_not_ge hstop132).le
  by_cases hstop133 : t ≤ stopTime R step133
  · exact global_step_range S_pos K_pos R_pos Q_pos sigma_mem cert133 hud hu133 t ⟨ht133,hstop133⟩
  have h133 := global_step_endpoint S_pos K_pos R_pos Q_pos sigma_mem cert133 hud hu133
  have hu134 := join_bound Q_pos join134 h133
  have ht134 : startTime R step134 ≤ t := by
    rw [start_eq_stop join134.1]
    exact (lt_of_not_ge hstop133).le
  by_cases hstop134 : t ≤ stopTime R step134
  · exact global_step_range S_pos K_pos R_pos Q_pos sigma_mem cert134 hud hu134 t ⟨ht134,hstop134⟩
  have h134 := global_step_endpoint S_pos K_pos R_pos Q_pos sigma_mem cert134 hud hu134
  have hu135 := join_bound Q_pos join135 h134
  have ht135 : startTime R step135 ≤ t := by
    rw [start_eq_stop join135.1]
    exact (lt_of_not_ge hstop134).le
  by_cases hstop135 : t ≤ stopTime R step135
  · exact global_step_range S_pos K_pos R_pos Q_pos sigma_mem cert135 hud hu135 t ⟨ht135,hstop135⟩
  have h135 := global_step_endpoint S_pos K_pos R_pos Q_pos sigma_mem cert135 hud hu135
  have hu136 := join_bound Q_pos join136 h135
  have ht136 : startTime R step136 ≤ t := by
    rw [start_eq_stop join136.1]
    exact (lt_of_not_ge hstop135).le
  by_cases hstop136 : t ≤ stopTime R step136
  · exact global_step_range S_pos K_pos R_pos Q_pos sigma_mem cert136 hud hu136 t ⟨ht136,hstop136⟩
  have h136 := global_step_endpoint S_pos K_pos R_pos Q_pos sigma_mem cert136 hud hu136
  have hu137 := join_bound Q_pos join137 h136
  have ht137 : startTime R step137 ≤ t := by
    rw [start_eq_stop join137.1]
    exact (lt_of_not_ge hstop136).le
  by_cases hstop137 : t ≤ stopTime R step137
  · exact global_step_range S_pos K_pos R_pos Q_pos sigma_mem cert137 hud hu137 t ⟨ht137,hstop137⟩
  have h137 := global_step_endpoint S_pos K_pos R_pos Q_pos sigma_mem cert137 hud hu137
  have hu138 := join_bound Q_pos join138 h137
  have ht138 : startTime R step138 ≤ t := by
    rw [start_eq_stop join138.1]
    exact (lt_of_not_ge hstop137).le
  by_cases hstop138 : t ≤ stopTime R step138
  · exact global_step_range S_pos K_pos R_pos Q_pos sigma_mem cert138 hud hu138 t ⟨ht138,hstop138⟩
  have h138 := global_step_endpoint S_pos K_pos R_pos Q_pos sigma_mem cert138 hud hu138
  have hu139 := join_bound Q_pos join139 h138
  have ht139 : startTime R step139 ≤ t := by
    rw [start_eq_stop join139.1]
    exact (lt_of_not_ge hstop138).le
  by_cases hstop139 : t ≤ stopTime R step139
  · exact global_step_range S_pos K_pos R_pos Q_pos sigma_mem cert139 hud hu139 t ⟨ht139,hstop139⟩
  have h139 := global_step_endpoint S_pos K_pos R_pos Q_pos sigma_mem cert139 hud hu139
  have hu140 := join_bound Q_pos join140 h139
  have ht140 : startTime R step140 ≤ t := by
    rw [start_eq_stop join140.1]
    exact (lt_of_not_ge hstop139).le
  by_cases hstop140 : t ≤ stopTime R step140
  · exact global_step_range S_pos K_pos R_pos Q_pos sigma_mem cert140 hud hu140 t ⟨ht140,hstop140⟩
  have h140 := global_step_endpoint S_pos K_pos R_pos Q_pos sigma_mem cert140 hud hu140
  have hu141 := join_bound Q_pos join141 h140
  have ht141 : startTime R step141 ≤ t := by
    rw [start_eq_stop join141.1]
    exact (lt_of_not_ge hstop140).le
  by_cases hstop141 : t ≤ stopTime R step141
  · exact global_step_range S_pos K_pos R_pos Q_pos sigma_mem cert141 hud hu141 t ⟨ht141,hstop141⟩
  have h141 := global_step_endpoint S_pos K_pos R_pos Q_pos sigma_mem cert141 hud hu141
  have hu142 := join_bound Q_pos join142 h141
  have ht142 : startTime R step142 ≤ t := by
    rw [start_eq_stop join142.1]
    exact (lt_of_not_ge hstop141).le
  by_cases hstop142 : t ≤ stopTime R step142
  · exact global_step_range S_pos K_pos R_pos Q_pos sigma_mem cert142 hud hu142 t ⟨ht142,hstop142⟩
  have h142 := global_step_endpoint S_pos K_pos R_pos Q_pos sigma_mem cert142 hud hu142
  have hu143 := join_bound Q_pos join143 h142
  have ht143 : startTime R step143 ≤ t := by
    rw [start_eq_stop join143.1]
    exact (lt_of_not_ge hstop142).le
  exact global_step_range S_pos K_pos R_pos Q_pos sigma_mem cert143 hud hu143 t ⟨ht143,ht.2⟩
theorem range_144 {u : ℝ → ℝ} (hud : ∀ t ∈ Icc (0:ℝ) (9/100), HasDerivWithinAt u
    (globalField (SN/S) (KN/K) t (u t)) (Icc 0 (9/100)) t)
    (hu : u (startTime R step144) ∈ Icc ((head step144.lo:ℝ)/Q) ((head step144.hi:ℝ)/Q)) :
    ∀ t ∈ Icc (startTime R step144) (stopTime R step159), u t ∈ Icc (0:ℝ) (999/1000) := by
  intro t ht
  have ht144 := ht.1
  by_cases hstop144 : t ≤ stopTime R step144
  · exact global_step_range S_pos K_pos R_pos Q_pos sigma_mem cert144 hud hu t ⟨ht144,hstop144⟩
  have h144 := global_step_endpoint S_pos K_pos R_pos Q_pos sigma_mem cert144 hud hu
  have hu145 := join_bound Q_pos join145 h144
  have ht145 : startTime R step145 ≤ t := by
    rw [start_eq_stop join145.1]
    exact (lt_of_not_ge hstop144).le
  by_cases hstop145 : t ≤ stopTime R step145
  · exact global_step_range S_pos K_pos R_pos Q_pos sigma_mem cert145 hud hu145 t ⟨ht145,hstop145⟩
  have h145 := global_step_endpoint S_pos K_pos R_pos Q_pos sigma_mem cert145 hud hu145
  have hu146 := join_bound Q_pos join146 h145
  have ht146 : startTime R step146 ≤ t := by
    rw [start_eq_stop join146.1]
    exact (lt_of_not_ge hstop145).le
  by_cases hstop146 : t ≤ stopTime R step146
  · exact global_step_range S_pos K_pos R_pos Q_pos sigma_mem cert146 hud hu146 t ⟨ht146,hstop146⟩
  have h146 := global_step_endpoint S_pos K_pos R_pos Q_pos sigma_mem cert146 hud hu146
  have hu147 := join_bound Q_pos join147 h146
  have ht147 : startTime R step147 ≤ t := by
    rw [start_eq_stop join147.1]
    exact (lt_of_not_ge hstop146).le
  by_cases hstop147 : t ≤ stopTime R step147
  · exact global_step_range S_pos K_pos R_pos Q_pos sigma_mem cert147 hud hu147 t ⟨ht147,hstop147⟩
  have h147 := global_step_endpoint S_pos K_pos R_pos Q_pos sigma_mem cert147 hud hu147
  have hu148 := join_bound Q_pos join148 h147
  have ht148 : startTime R step148 ≤ t := by
    rw [start_eq_stop join148.1]
    exact (lt_of_not_ge hstop147).le
  by_cases hstop148 : t ≤ stopTime R step148
  · exact global_step_range S_pos K_pos R_pos Q_pos sigma_mem cert148 hud hu148 t ⟨ht148,hstop148⟩
  have h148 := global_step_endpoint S_pos K_pos R_pos Q_pos sigma_mem cert148 hud hu148
  have hu149 := join_bound Q_pos join149 h148
  have ht149 : startTime R step149 ≤ t := by
    rw [start_eq_stop join149.1]
    exact (lt_of_not_ge hstop148).le
  by_cases hstop149 : t ≤ stopTime R step149
  · exact global_step_range S_pos K_pos R_pos Q_pos sigma_mem cert149 hud hu149 t ⟨ht149,hstop149⟩
  have h149 := global_step_endpoint S_pos K_pos R_pos Q_pos sigma_mem cert149 hud hu149
  have hu150 := join_bound Q_pos join150 h149
  have ht150 : startTime R step150 ≤ t := by
    rw [start_eq_stop join150.1]
    exact (lt_of_not_ge hstop149).le
  by_cases hstop150 : t ≤ stopTime R step150
  · exact global_step_range S_pos K_pos R_pos Q_pos sigma_mem cert150 hud hu150 t ⟨ht150,hstop150⟩
  have h150 := global_step_endpoint S_pos K_pos R_pos Q_pos sigma_mem cert150 hud hu150
  have hu151 := join_bound Q_pos join151 h150
  have ht151 : startTime R step151 ≤ t := by
    rw [start_eq_stop join151.1]
    exact (lt_of_not_ge hstop150).le
  by_cases hstop151 : t ≤ stopTime R step151
  · exact global_step_range S_pos K_pos R_pos Q_pos sigma_mem cert151 hud hu151 t ⟨ht151,hstop151⟩
  have h151 := global_step_endpoint S_pos K_pos R_pos Q_pos sigma_mem cert151 hud hu151
  have hu152 := join_bound Q_pos join152 h151
  have ht152 : startTime R step152 ≤ t := by
    rw [start_eq_stop join152.1]
    exact (lt_of_not_ge hstop151).le
  by_cases hstop152 : t ≤ stopTime R step152
  · exact global_step_range S_pos K_pos R_pos Q_pos sigma_mem cert152 hud hu152 t ⟨ht152,hstop152⟩
  have h152 := global_step_endpoint S_pos K_pos R_pos Q_pos sigma_mem cert152 hud hu152
  have hu153 := join_bound Q_pos join153 h152
  have ht153 : startTime R step153 ≤ t := by
    rw [start_eq_stop join153.1]
    exact (lt_of_not_ge hstop152).le
  by_cases hstop153 : t ≤ stopTime R step153
  · exact global_step_range S_pos K_pos R_pos Q_pos sigma_mem cert153 hud hu153 t ⟨ht153,hstop153⟩
  have h153 := global_step_endpoint S_pos K_pos R_pos Q_pos sigma_mem cert153 hud hu153
  have hu154 := join_bound Q_pos join154 h153
  have ht154 : startTime R step154 ≤ t := by
    rw [start_eq_stop join154.1]
    exact (lt_of_not_ge hstop153).le
  by_cases hstop154 : t ≤ stopTime R step154
  · exact global_step_range S_pos K_pos R_pos Q_pos sigma_mem cert154 hud hu154 t ⟨ht154,hstop154⟩
  have h154 := global_step_endpoint S_pos K_pos R_pos Q_pos sigma_mem cert154 hud hu154
  have hu155 := join_bound Q_pos join155 h154
  have ht155 : startTime R step155 ≤ t := by
    rw [start_eq_stop join155.1]
    exact (lt_of_not_ge hstop154).le
  by_cases hstop155 : t ≤ stopTime R step155
  · exact global_step_range S_pos K_pos R_pos Q_pos sigma_mem cert155 hud hu155 t ⟨ht155,hstop155⟩
  have h155 := global_step_endpoint S_pos K_pos R_pos Q_pos sigma_mem cert155 hud hu155
  have hu156 := join_bound Q_pos join156 h155
  have ht156 : startTime R step156 ≤ t := by
    rw [start_eq_stop join156.1]
    exact (lt_of_not_ge hstop155).le
  by_cases hstop156 : t ≤ stopTime R step156
  · exact global_step_range S_pos K_pos R_pos Q_pos sigma_mem cert156 hud hu156 t ⟨ht156,hstop156⟩
  have h156 := global_step_endpoint S_pos K_pos R_pos Q_pos sigma_mem cert156 hud hu156
  have hu157 := join_bound Q_pos join157 h156
  have ht157 : startTime R step157 ≤ t := by
    rw [start_eq_stop join157.1]
    exact (lt_of_not_ge hstop156).le
  by_cases hstop157 : t ≤ stopTime R step157
  · exact global_step_range S_pos K_pos R_pos Q_pos sigma_mem cert157 hud hu157 t ⟨ht157,hstop157⟩
  have h157 := global_step_endpoint S_pos K_pos R_pos Q_pos sigma_mem cert157 hud hu157
  have hu158 := join_bound Q_pos join158 h157
  have ht158 : startTime R step158 ≤ t := by
    rw [start_eq_stop join158.1]
    exact (lt_of_not_ge hstop157).le
  by_cases hstop158 : t ≤ stopTime R step158
  · exact global_step_range S_pos K_pos R_pos Q_pos sigma_mem cert158 hud hu158 t ⟨ht158,hstop158⟩
  have h158 := global_step_endpoint S_pos K_pos R_pos Q_pos sigma_mem cert158 hud hu158
  have hu159 := join_bound Q_pos join159 h158
  have ht159 : startTime R step159 ≤ t := by
    rw [start_eq_stop join159.1]
    exact (lt_of_not_ge hstop158).le
  exact global_step_range S_pos K_pos R_pos Q_pos sigma_mem cert159 hud hu159 t ⟨ht159,ht.2⟩
theorem range_160 {u : ℝ → ℝ} (hud : ∀ t ∈ Icc (0:ℝ) (9/100), HasDerivWithinAt u
    (globalField (SN/S) (KN/K) t (u t)) (Icc 0 (9/100)) t)
    (hu : u (startTime R step160) ∈ Icc ((head step160.lo:ℝ)/Q) ((head step160.hi:ℝ)/Q)) :
    ∀ t ∈ Icc (startTime R step160) (stopTime R step175), u t ∈ Icc (0:ℝ) (999/1000) := by
  intro t ht
  have ht160 := ht.1
  by_cases hstop160 : t ≤ stopTime R step160
  · exact global_step_range S_pos K_pos R_pos Q_pos sigma_mem cert160 hud hu t ⟨ht160,hstop160⟩
  have h160 := global_step_endpoint S_pos K_pos R_pos Q_pos sigma_mem cert160 hud hu
  have hu161 := join_bound Q_pos join161 h160
  have ht161 : startTime R step161 ≤ t := by
    rw [start_eq_stop join161.1]
    exact (lt_of_not_ge hstop160).le
  by_cases hstop161 : t ≤ stopTime R step161
  · exact global_step_range S_pos K_pos R_pos Q_pos sigma_mem cert161 hud hu161 t ⟨ht161,hstop161⟩
  have h161 := global_step_endpoint S_pos K_pos R_pos Q_pos sigma_mem cert161 hud hu161
  have hu162 := join_bound Q_pos join162 h161
  have ht162 : startTime R step162 ≤ t := by
    rw [start_eq_stop join162.1]
    exact (lt_of_not_ge hstop161).le
  by_cases hstop162 : t ≤ stopTime R step162
  · exact global_step_range S_pos K_pos R_pos Q_pos sigma_mem cert162 hud hu162 t ⟨ht162,hstop162⟩
  have h162 := global_step_endpoint S_pos K_pos R_pos Q_pos sigma_mem cert162 hud hu162
  have hu163 := join_bound Q_pos join163 h162
  have ht163 : startTime R step163 ≤ t := by
    rw [start_eq_stop join163.1]
    exact (lt_of_not_ge hstop162).le
  by_cases hstop163 : t ≤ stopTime R step163
  · exact global_step_range S_pos K_pos R_pos Q_pos sigma_mem cert163 hud hu163 t ⟨ht163,hstop163⟩
  have h163 := global_step_endpoint S_pos K_pos R_pos Q_pos sigma_mem cert163 hud hu163
  have hu164 := join_bound Q_pos join164 h163
  have ht164 : startTime R step164 ≤ t := by
    rw [start_eq_stop join164.1]
    exact (lt_of_not_ge hstop163).le
  by_cases hstop164 : t ≤ stopTime R step164
  · exact global_step_range S_pos K_pos R_pos Q_pos sigma_mem cert164 hud hu164 t ⟨ht164,hstop164⟩
  have h164 := global_step_endpoint S_pos K_pos R_pos Q_pos sigma_mem cert164 hud hu164
  have hu165 := join_bound Q_pos join165 h164
  have ht165 : startTime R step165 ≤ t := by
    rw [start_eq_stop join165.1]
    exact (lt_of_not_ge hstop164).le
  by_cases hstop165 : t ≤ stopTime R step165
  · exact global_step_range S_pos K_pos R_pos Q_pos sigma_mem cert165 hud hu165 t ⟨ht165,hstop165⟩
  have h165 := global_step_endpoint S_pos K_pos R_pos Q_pos sigma_mem cert165 hud hu165
  have hu166 := join_bound Q_pos join166 h165
  have ht166 : startTime R step166 ≤ t := by
    rw [start_eq_stop join166.1]
    exact (lt_of_not_ge hstop165).le
  by_cases hstop166 : t ≤ stopTime R step166
  · exact global_step_range S_pos K_pos R_pos Q_pos sigma_mem cert166 hud hu166 t ⟨ht166,hstop166⟩
  have h166 := global_step_endpoint S_pos K_pos R_pos Q_pos sigma_mem cert166 hud hu166
  have hu167 := join_bound Q_pos join167 h166
  have ht167 : startTime R step167 ≤ t := by
    rw [start_eq_stop join167.1]
    exact (lt_of_not_ge hstop166).le
  by_cases hstop167 : t ≤ stopTime R step167
  · exact global_step_range S_pos K_pos R_pos Q_pos sigma_mem cert167 hud hu167 t ⟨ht167,hstop167⟩
  have h167 := global_step_endpoint S_pos K_pos R_pos Q_pos sigma_mem cert167 hud hu167
  have hu168 := join_bound Q_pos join168 h167
  have ht168 : startTime R step168 ≤ t := by
    rw [start_eq_stop join168.1]
    exact (lt_of_not_ge hstop167).le
  by_cases hstop168 : t ≤ stopTime R step168
  · exact global_step_range S_pos K_pos R_pos Q_pos sigma_mem cert168 hud hu168 t ⟨ht168,hstop168⟩
  have h168 := global_step_endpoint S_pos K_pos R_pos Q_pos sigma_mem cert168 hud hu168
  have hu169 := join_bound Q_pos join169 h168
  have ht169 : startTime R step169 ≤ t := by
    rw [start_eq_stop join169.1]
    exact (lt_of_not_ge hstop168).le
  by_cases hstop169 : t ≤ stopTime R step169
  · exact global_step_range S_pos K_pos R_pos Q_pos sigma_mem cert169 hud hu169 t ⟨ht169,hstop169⟩
  have h169 := global_step_endpoint S_pos K_pos R_pos Q_pos sigma_mem cert169 hud hu169
  have hu170 := join_bound Q_pos join170 h169
  have ht170 : startTime R step170 ≤ t := by
    rw [start_eq_stop join170.1]
    exact (lt_of_not_ge hstop169).le
  by_cases hstop170 : t ≤ stopTime R step170
  · exact global_step_range S_pos K_pos R_pos Q_pos sigma_mem cert170 hud hu170 t ⟨ht170,hstop170⟩
  have h170 := global_step_endpoint S_pos K_pos R_pos Q_pos sigma_mem cert170 hud hu170
  have hu171 := join_bound Q_pos join171 h170
  have ht171 : startTime R step171 ≤ t := by
    rw [start_eq_stop join171.1]
    exact (lt_of_not_ge hstop170).le
  by_cases hstop171 : t ≤ stopTime R step171
  · exact global_step_range S_pos K_pos R_pos Q_pos sigma_mem cert171 hud hu171 t ⟨ht171,hstop171⟩
  have h171 := global_step_endpoint S_pos K_pos R_pos Q_pos sigma_mem cert171 hud hu171
  have hu172 := join_bound Q_pos join172 h171
  have ht172 : startTime R step172 ≤ t := by
    rw [start_eq_stop join172.1]
    exact (lt_of_not_ge hstop171).le
  by_cases hstop172 : t ≤ stopTime R step172
  · exact global_step_range S_pos K_pos R_pos Q_pos sigma_mem cert172 hud hu172 t ⟨ht172,hstop172⟩
  have h172 := global_step_endpoint S_pos K_pos R_pos Q_pos sigma_mem cert172 hud hu172
  have hu173 := join_bound Q_pos join173 h172
  have ht173 : startTime R step173 ≤ t := by
    rw [start_eq_stop join173.1]
    exact (lt_of_not_ge hstop172).le
  by_cases hstop173 : t ≤ stopTime R step173
  · exact global_step_range S_pos K_pos R_pos Q_pos sigma_mem cert173 hud hu173 t ⟨ht173,hstop173⟩
  have h173 := global_step_endpoint S_pos K_pos R_pos Q_pos sigma_mem cert173 hud hu173
  have hu174 := join_bound Q_pos join174 h173
  have ht174 : startTime R step174 ≤ t := by
    rw [start_eq_stop join174.1]
    exact (lt_of_not_ge hstop173).le
  by_cases hstop174 : t ≤ stopTime R step174
  · exact global_step_range S_pos K_pos R_pos Q_pos sigma_mem cert174 hud hu174 t ⟨ht174,hstop174⟩
  have h174 := global_step_endpoint S_pos K_pos R_pos Q_pos sigma_mem cert174 hud hu174
  have hu175 := join_bound Q_pos join175 h174
  have ht175 : startTime R step175 ≤ t := by
    rw [start_eq_stop join175.1]
    exact (lt_of_not_ge hstop174).le
  exact global_step_range S_pos K_pos R_pos Q_pos sigma_mem cert175 hud hu175 t ⟨ht175,ht.2⟩
theorem range_176 {u : ℝ → ℝ} (hud : ∀ t ∈ Icc (0:ℝ) (9/100), HasDerivWithinAt u
    (globalField (SN/S) (KN/K) t (u t)) (Icc 0 (9/100)) t)
    (hu : u (startTime R step176) ∈ Icc ((head step176.lo:ℝ)/Q) ((head step176.hi:ℝ)/Q)) :
    ∀ t ∈ Icc (startTime R step176) (stopTime R step191), u t ∈ Icc (0:ℝ) (999/1000) := by
  intro t ht
  have ht176 := ht.1
  by_cases hstop176 : t ≤ stopTime R step176
  · exact global_step_range S_pos K_pos R_pos Q_pos sigma_mem cert176 hud hu t ⟨ht176,hstop176⟩
  have h176 := global_step_endpoint S_pos K_pos R_pos Q_pos sigma_mem cert176 hud hu
  have hu177 := join_bound Q_pos join177 h176
  have ht177 : startTime R step177 ≤ t := by
    rw [start_eq_stop join177.1]
    exact (lt_of_not_ge hstop176).le
  by_cases hstop177 : t ≤ stopTime R step177
  · exact global_step_range S_pos K_pos R_pos Q_pos sigma_mem cert177 hud hu177 t ⟨ht177,hstop177⟩
  have h177 := global_step_endpoint S_pos K_pos R_pos Q_pos sigma_mem cert177 hud hu177
  have hu178 := join_bound Q_pos join178 h177
  have ht178 : startTime R step178 ≤ t := by
    rw [start_eq_stop join178.1]
    exact (lt_of_not_ge hstop177).le
  by_cases hstop178 : t ≤ stopTime R step178
  · exact global_step_range S_pos K_pos R_pos Q_pos sigma_mem cert178 hud hu178 t ⟨ht178,hstop178⟩
  have h178 := global_step_endpoint S_pos K_pos R_pos Q_pos sigma_mem cert178 hud hu178
  have hu179 := join_bound Q_pos join179 h178
  have ht179 : startTime R step179 ≤ t := by
    rw [start_eq_stop join179.1]
    exact (lt_of_not_ge hstop178).le
  by_cases hstop179 : t ≤ stopTime R step179
  · exact global_step_range S_pos K_pos R_pos Q_pos sigma_mem cert179 hud hu179 t ⟨ht179,hstop179⟩
  have h179 := global_step_endpoint S_pos K_pos R_pos Q_pos sigma_mem cert179 hud hu179
  have hu180 := join_bound Q_pos join180 h179
  have ht180 : startTime R step180 ≤ t := by
    rw [start_eq_stop join180.1]
    exact (lt_of_not_ge hstop179).le
  by_cases hstop180 : t ≤ stopTime R step180
  · exact global_step_range S_pos K_pos R_pos Q_pos sigma_mem cert180 hud hu180 t ⟨ht180,hstop180⟩
  have h180 := global_step_endpoint S_pos K_pos R_pos Q_pos sigma_mem cert180 hud hu180
  have hu181 := join_bound Q_pos join181 h180
  have ht181 : startTime R step181 ≤ t := by
    rw [start_eq_stop join181.1]
    exact (lt_of_not_ge hstop180).le
  by_cases hstop181 : t ≤ stopTime R step181
  · exact global_step_range S_pos K_pos R_pos Q_pos sigma_mem cert181 hud hu181 t ⟨ht181,hstop181⟩
  have h181 := global_step_endpoint S_pos K_pos R_pos Q_pos sigma_mem cert181 hud hu181
  have hu182 := join_bound Q_pos join182 h181
  have ht182 : startTime R step182 ≤ t := by
    rw [start_eq_stop join182.1]
    exact (lt_of_not_ge hstop181).le
  by_cases hstop182 : t ≤ stopTime R step182
  · exact global_step_range S_pos K_pos R_pos Q_pos sigma_mem cert182 hud hu182 t ⟨ht182,hstop182⟩
  have h182 := global_step_endpoint S_pos K_pos R_pos Q_pos sigma_mem cert182 hud hu182
  have hu183 := join_bound Q_pos join183 h182
  have ht183 : startTime R step183 ≤ t := by
    rw [start_eq_stop join183.1]
    exact (lt_of_not_ge hstop182).le
  by_cases hstop183 : t ≤ stopTime R step183
  · exact global_step_range S_pos K_pos R_pos Q_pos sigma_mem cert183 hud hu183 t ⟨ht183,hstop183⟩
  have h183 := global_step_endpoint S_pos K_pos R_pos Q_pos sigma_mem cert183 hud hu183
  have hu184 := join_bound Q_pos join184 h183
  have ht184 : startTime R step184 ≤ t := by
    rw [start_eq_stop join184.1]
    exact (lt_of_not_ge hstop183).le
  by_cases hstop184 : t ≤ stopTime R step184
  · exact global_step_range S_pos K_pos R_pos Q_pos sigma_mem cert184 hud hu184 t ⟨ht184,hstop184⟩
  have h184 := global_step_endpoint S_pos K_pos R_pos Q_pos sigma_mem cert184 hud hu184
  have hu185 := join_bound Q_pos join185 h184
  have ht185 : startTime R step185 ≤ t := by
    rw [start_eq_stop join185.1]
    exact (lt_of_not_ge hstop184).le
  by_cases hstop185 : t ≤ stopTime R step185
  · exact global_step_range S_pos K_pos R_pos Q_pos sigma_mem cert185 hud hu185 t ⟨ht185,hstop185⟩
  have h185 := global_step_endpoint S_pos K_pos R_pos Q_pos sigma_mem cert185 hud hu185
  have hu186 := join_bound Q_pos join186 h185
  have ht186 : startTime R step186 ≤ t := by
    rw [start_eq_stop join186.1]
    exact (lt_of_not_ge hstop185).le
  by_cases hstop186 : t ≤ stopTime R step186
  · exact global_step_range S_pos K_pos R_pos Q_pos sigma_mem cert186 hud hu186 t ⟨ht186,hstop186⟩
  have h186 := global_step_endpoint S_pos K_pos R_pos Q_pos sigma_mem cert186 hud hu186
  have hu187 := join_bound Q_pos join187 h186
  have ht187 : startTime R step187 ≤ t := by
    rw [start_eq_stop join187.1]
    exact (lt_of_not_ge hstop186).le
  by_cases hstop187 : t ≤ stopTime R step187
  · exact global_step_range S_pos K_pos R_pos Q_pos sigma_mem cert187 hud hu187 t ⟨ht187,hstop187⟩
  have h187 := global_step_endpoint S_pos K_pos R_pos Q_pos sigma_mem cert187 hud hu187
  have hu188 := join_bound Q_pos join188 h187
  have ht188 : startTime R step188 ≤ t := by
    rw [start_eq_stop join188.1]
    exact (lt_of_not_ge hstop187).le
  by_cases hstop188 : t ≤ stopTime R step188
  · exact global_step_range S_pos K_pos R_pos Q_pos sigma_mem cert188 hud hu188 t ⟨ht188,hstop188⟩
  have h188 := global_step_endpoint S_pos K_pos R_pos Q_pos sigma_mem cert188 hud hu188
  have hu189 := join_bound Q_pos join189 h188
  have ht189 : startTime R step189 ≤ t := by
    rw [start_eq_stop join189.1]
    exact (lt_of_not_ge hstop188).le
  by_cases hstop189 : t ≤ stopTime R step189
  · exact global_step_range S_pos K_pos R_pos Q_pos sigma_mem cert189 hud hu189 t ⟨ht189,hstop189⟩
  have h189 := global_step_endpoint S_pos K_pos R_pos Q_pos sigma_mem cert189 hud hu189
  have hu190 := join_bound Q_pos join190 h189
  have ht190 : startTime R step190 ≤ t := by
    rw [start_eq_stop join190.1]
    exact (lt_of_not_ge hstop189).le
  by_cases hstop190 : t ≤ stopTime R step190
  · exact global_step_range S_pos K_pos R_pos Q_pos sigma_mem cert190 hud hu190 t ⟨ht190,hstop190⟩
  have h190 := global_step_endpoint S_pos K_pos R_pos Q_pos sigma_mem cert190 hud hu190
  have hu191 := join_bound Q_pos join191 h190
  have ht191 : startTime R step191 ≤ t := by
    rw [start_eq_stop join191.1]
    exact (lt_of_not_ge hstop190).le
  exact global_step_range S_pos K_pos R_pos Q_pos sigma_mem cert191 hud hu191 t ⟨ht191,ht.2⟩
theorem range_192 {u : ℝ → ℝ} (hud : ∀ t ∈ Icc (0:ℝ) (9/100), HasDerivWithinAt u
    (globalField (SN/S) (KN/K) t (u t)) (Icc 0 (9/100)) t)
    (hu : u (startTime R step192) ∈ Icc ((head step192.lo:ℝ)/Q) ((head step192.hi:ℝ)/Q)) :
    ∀ t ∈ Icc (startTime R step192) (stopTime R step207), u t ∈ Icc (0:ℝ) (999/1000) := by
  intro t ht
  have ht192 := ht.1
  by_cases hstop192 : t ≤ stopTime R step192
  · exact global_step_range S_pos K_pos R_pos Q_pos sigma_mem cert192 hud hu t ⟨ht192,hstop192⟩
  have h192 := global_step_endpoint S_pos K_pos R_pos Q_pos sigma_mem cert192 hud hu
  have hu193 := join_bound Q_pos join193 h192
  have ht193 : startTime R step193 ≤ t := by
    rw [start_eq_stop join193.1]
    exact (lt_of_not_ge hstop192).le
  by_cases hstop193 : t ≤ stopTime R step193
  · exact global_step_range S_pos K_pos R_pos Q_pos sigma_mem cert193 hud hu193 t ⟨ht193,hstop193⟩
  have h193 := global_step_endpoint S_pos K_pos R_pos Q_pos sigma_mem cert193 hud hu193
  have hu194 := join_bound Q_pos join194 h193
  have ht194 : startTime R step194 ≤ t := by
    rw [start_eq_stop join194.1]
    exact (lt_of_not_ge hstop193).le
  by_cases hstop194 : t ≤ stopTime R step194
  · exact global_step_range S_pos K_pos R_pos Q_pos sigma_mem cert194 hud hu194 t ⟨ht194,hstop194⟩
  have h194 := global_step_endpoint S_pos K_pos R_pos Q_pos sigma_mem cert194 hud hu194
  have hu195 := join_bound Q_pos join195 h194
  have ht195 : startTime R step195 ≤ t := by
    rw [start_eq_stop join195.1]
    exact (lt_of_not_ge hstop194).le
  by_cases hstop195 : t ≤ stopTime R step195
  · exact global_step_range S_pos K_pos R_pos Q_pos sigma_mem cert195 hud hu195 t ⟨ht195,hstop195⟩
  have h195 := global_step_endpoint S_pos K_pos R_pos Q_pos sigma_mem cert195 hud hu195
  have hu196 := join_bound Q_pos join196 h195
  have ht196 : startTime R step196 ≤ t := by
    rw [start_eq_stop join196.1]
    exact (lt_of_not_ge hstop195).le
  by_cases hstop196 : t ≤ stopTime R step196
  · exact global_step_range S_pos K_pos R_pos Q_pos sigma_mem cert196 hud hu196 t ⟨ht196,hstop196⟩
  have h196 := global_step_endpoint S_pos K_pos R_pos Q_pos sigma_mem cert196 hud hu196
  have hu197 := join_bound Q_pos join197 h196
  have ht197 : startTime R step197 ≤ t := by
    rw [start_eq_stop join197.1]
    exact (lt_of_not_ge hstop196).le
  by_cases hstop197 : t ≤ stopTime R step197
  · exact global_step_range S_pos K_pos R_pos Q_pos sigma_mem cert197 hud hu197 t ⟨ht197,hstop197⟩
  have h197 := global_step_endpoint S_pos K_pos R_pos Q_pos sigma_mem cert197 hud hu197
  have hu198 := join_bound Q_pos join198 h197
  have ht198 : startTime R step198 ≤ t := by
    rw [start_eq_stop join198.1]
    exact (lt_of_not_ge hstop197).le
  by_cases hstop198 : t ≤ stopTime R step198
  · exact global_step_range S_pos K_pos R_pos Q_pos sigma_mem cert198 hud hu198 t ⟨ht198,hstop198⟩
  have h198 := global_step_endpoint S_pos K_pos R_pos Q_pos sigma_mem cert198 hud hu198
  have hu199 := join_bound Q_pos join199 h198
  have ht199 : startTime R step199 ≤ t := by
    rw [start_eq_stop join199.1]
    exact (lt_of_not_ge hstop198).le
  by_cases hstop199 : t ≤ stopTime R step199
  · exact global_step_range S_pos K_pos R_pos Q_pos sigma_mem cert199 hud hu199 t ⟨ht199,hstop199⟩
  have h199 := global_step_endpoint S_pos K_pos R_pos Q_pos sigma_mem cert199 hud hu199
  have hu200 := join_bound Q_pos join200 h199
  have ht200 : startTime R step200 ≤ t := by
    rw [start_eq_stop join200.1]
    exact (lt_of_not_ge hstop199).le
  by_cases hstop200 : t ≤ stopTime R step200
  · exact global_step_range S_pos K_pos R_pos Q_pos sigma_mem cert200 hud hu200 t ⟨ht200,hstop200⟩
  have h200 := global_step_endpoint S_pos K_pos R_pos Q_pos sigma_mem cert200 hud hu200
  have hu201 := join_bound Q_pos join201 h200
  have ht201 : startTime R step201 ≤ t := by
    rw [start_eq_stop join201.1]
    exact (lt_of_not_ge hstop200).le
  by_cases hstop201 : t ≤ stopTime R step201
  · exact global_step_range S_pos K_pos R_pos Q_pos sigma_mem cert201 hud hu201 t ⟨ht201,hstop201⟩
  have h201 := global_step_endpoint S_pos K_pos R_pos Q_pos sigma_mem cert201 hud hu201
  have hu202 := join_bound Q_pos join202 h201
  have ht202 : startTime R step202 ≤ t := by
    rw [start_eq_stop join202.1]
    exact (lt_of_not_ge hstop201).le
  by_cases hstop202 : t ≤ stopTime R step202
  · exact global_step_range S_pos K_pos R_pos Q_pos sigma_mem cert202 hud hu202 t ⟨ht202,hstop202⟩
  have h202 := global_step_endpoint S_pos K_pos R_pos Q_pos sigma_mem cert202 hud hu202
  have hu203 := join_bound Q_pos join203 h202
  have ht203 : startTime R step203 ≤ t := by
    rw [start_eq_stop join203.1]
    exact (lt_of_not_ge hstop202).le
  by_cases hstop203 : t ≤ stopTime R step203
  · exact global_step_range S_pos K_pos R_pos Q_pos sigma_mem cert203 hud hu203 t ⟨ht203,hstop203⟩
  have h203 := global_step_endpoint S_pos K_pos R_pos Q_pos sigma_mem cert203 hud hu203
  have hu204 := join_bound Q_pos join204 h203
  have ht204 : startTime R step204 ≤ t := by
    rw [start_eq_stop join204.1]
    exact (lt_of_not_ge hstop203).le
  by_cases hstop204 : t ≤ stopTime R step204
  · exact global_step_range S_pos K_pos R_pos Q_pos sigma_mem cert204 hud hu204 t ⟨ht204,hstop204⟩
  have h204 := global_step_endpoint S_pos K_pos R_pos Q_pos sigma_mem cert204 hud hu204
  have hu205 := join_bound Q_pos join205 h204
  have ht205 : startTime R step205 ≤ t := by
    rw [start_eq_stop join205.1]
    exact (lt_of_not_ge hstop204).le
  by_cases hstop205 : t ≤ stopTime R step205
  · exact global_step_range S_pos K_pos R_pos Q_pos sigma_mem cert205 hud hu205 t ⟨ht205,hstop205⟩
  have h205 := global_step_endpoint S_pos K_pos R_pos Q_pos sigma_mem cert205 hud hu205
  have hu206 := join_bound Q_pos join206 h205
  have ht206 : startTime R step206 ≤ t := by
    rw [start_eq_stop join206.1]
    exact (lt_of_not_ge hstop205).le
  by_cases hstop206 : t ≤ stopTime R step206
  · exact global_step_range S_pos K_pos R_pos Q_pos sigma_mem cert206 hud hu206 t ⟨ht206,hstop206⟩
  have h206 := global_step_endpoint S_pos K_pos R_pos Q_pos sigma_mem cert206 hud hu206
  have hu207 := join_bound Q_pos join207 h206
  have ht207 : startTime R step207 ≤ t := by
    rw [start_eq_stop join207.1]
    exact (lt_of_not_ge hstop206).le
  exact global_step_range S_pos K_pos R_pos Q_pos sigma_mem cert207 hud hu207 t ⟨ht207,ht.2⟩
theorem range_208 {u : ℝ → ℝ} (hud : ∀ t ∈ Icc (0:ℝ) (9/100), HasDerivWithinAt u
    (globalField (SN/S) (KN/K) t (u t)) (Icc 0 (9/100)) t)
    (hu : u (startTime R step208) ∈ Icc ((head step208.lo:ℝ)/Q) ((head step208.hi:ℝ)/Q)) :
    ∀ t ∈ Icc (startTime R step208) (stopTime R step223), u t ∈ Icc (0:ℝ) (999/1000) := by
  intro t ht
  have ht208 := ht.1
  by_cases hstop208 : t ≤ stopTime R step208
  · exact global_step_range S_pos K_pos R_pos Q_pos sigma_mem cert208 hud hu t ⟨ht208,hstop208⟩
  have h208 := global_step_endpoint S_pos K_pos R_pos Q_pos sigma_mem cert208 hud hu
  have hu209 := join_bound Q_pos join209 h208
  have ht209 : startTime R step209 ≤ t := by
    rw [start_eq_stop join209.1]
    exact (lt_of_not_ge hstop208).le
  by_cases hstop209 : t ≤ stopTime R step209
  · exact global_step_range S_pos K_pos R_pos Q_pos sigma_mem cert209 hud hu209 t ⟨ht209,hstop209⟩
  have h209 := global_step_endpoint S_pos K_pos R_pos Q_pos sigma_mem cert209 hud hu209
  have hu210 := join_bound Q_pos join210 h209
  have ht210 : startTime R step210 ≤ t := by
    rw [start_eq_stop join210.1]
    exact (lt_of_not_ge hstop209).le
  by_cases hstop210 : t ≤ stopTime R step210
  · exact global_step_range S_pos K_pos R_pos Q_pos sigma_mem cert210 hud hu210 t ⟨ht210,hstop210⟩
  have h210 := global_step_endpoint S_pos K_pos R_pos Q_pos sigma_mem cert210 hud hu210
  have hu211 := join_bound Q_pos join211 h210
  have ht211 : startTime R step211 ≤ t := by
    rw [start_eq_stop join211.1]
    exact (lt_of_not_ge hstop210).le
  by_cases hstop211 : t ≤ stopTime R step211
  · exact global_step_range S_pos K_pos R_pos Q_pos sigma_mem cert211 hud hu211 t ⟨ht211,hstop211⟩
  have h211 := global_step_endpoint S_pos K_pos R_pos Q_pos sigma_mem cert211 hud hu211
  have hu212 := join_bound Q_pos join212 h211
  have ht212 : startTime R step212 ≤ t := by
    rw [start_eq_stop join212.1]
    exact (lt_of_not_ge hstop211).le
  by_cases hstop212 : t ≤ stopTime R step212
  · exact global_step_range S_pos K_pos R_pos Q_pos sigma_mem cert212 hud hu212 t ⟨ht212,hstop212⟩
  have h212 := global_step_endpoint S_pos K_pos R_pos Q_pos sigma_mem cert212 hud hu212
  have hu213 := join_bound Q_pos join213 h212
  have ht213 : startTime R step213 ≤ t := by
    rw [start_eq_stop join213.1]
    exact (lt_of_not_ge hstop212).le
  by_cases hstop213 : t ≤ stopTime R step213
  · exact global_step_range S_pos K_pos R_pos Q_pos sigma_mem cert213 hud hu213 t ⟨ht213,hstop213⟩
  have h213 := global_step_endpoint S_pos K_pos R_pos Q_pos sigma_mem cert213 hud hu213
  have hu214 := join_bound Q_pos join214 h213
  have ht214 : startTime R step214 ≤ t := by
    rw [start_eq_stop join214.1]
    exact (lt_of_not_ge hstop213).le
  by_cases hstop214 : t ≤ stopTime R step214
  · exact global_step_range S_pos K_pos R_pos Q_pos sigma_mem cert214 hud hu214 t ⟨ht214,hstop214⟩
  have h214 := global_step_endpoint S_pos K_pos R_pos Q_pos sigma_mem cert214 hud hu214
  have hu215 := join_bound Q_pos join215 h214
  have ht215 : startTime R step215 ≤ t := by
    rw [start_eq_stop join215.1]
    exact (lt_of_not_ge hstop214).le
  by_cases hstop215 : t ≤ stopTime R step215
  · exact global_step_range S_pos K_pos R_pos Q_pos sigma_mem cert215 hud hu215 t ⟨ht215,hstop215⟩
  have h215 := global_step_endpoint S_pos K_pos R_pos Q_pos sigma_mem cert215 hud hu215
  have hu216 := join_bound Q_pos join216 h215
  have ht216 : startTime R step216 ≤ t := by
    rw [start_eq_stop join216.1]
    exact (lt_of_not_ge hstop215).le
  by_cases hstop216 : t ≤ stopTime R step216
  · exact global_step_range S_pos K_pos R_pos Q_pos sigma_mem cert216 hud hu216 t ⟨ht216,hstop216⟩
  have h216 := global_step_endpoint S_pos K_pos R_pos Q_pos sigma_mem cert216 hud hu216
  have hu217 := join_bound Q_pos join217 h216
  have ht217 : startTime R step217 ≤ t := by
    rw [start_eq_stop join217.1]
    exact (lt_of_not_ge hstop216).le
  by_cases hstop217 : t ≤ stopTime R step217
  · exact global_step_range S_pos K_pos R_pos Q_pos sigma_mem cert217 hud hu217 t ⟨ht217,hstop217⟩
  have h217 := global_step_endpoint S_pos K_pos R_pos Q_pos sigma_mem cert217 hud hu217
  have hu218 := join_bound Q_pos join218 h217
  have ht218 : startTime R step218 ≤ t := by
    rw [start_eq_stop join218.1]
    exact (lt_of_not_ge hstop217).le
  by_cases hstop218 : t ≤ stopTime R step218
  · exact global_step_range S_pos K_pos R_pos Q_pos sigma_mem cert218 hud hu218 t ⟨ht218,hstop218⟩
  have h218 := global_step_endpoint S_pos K_pos R_pos Q_pos sigma_mem cert218 hud hu218
  have hu219 := join_bound Q_pos join219 h218
  have ht219 : startTime R step219 ≤ t := by
    rw [start_eq_stop join219.1]
    exact (lt_of_not_ge hstop218).le
  by_cases hstop219 : t ≤ stopTime R step219
  · exact global_step_range S_pos K_pos R_pos Q_pos sigma_mem cert219 hud hu219 t ⟨ht219,hstop219⟩
  have h219 := global_step_endpoint S_pos K_pos R_pos Q_pos sigma_mem cert219 hud hu219
  have hu220 := join_bound Q_pos join220 h219
  have ht220 : startTime R step220 ≤ t := by
    rw [start_eq_stop join220.1]
    exact (lt_of_not_ge hstop219).le
  by_cases hstop220 : t ≤ stopTime R step220
  · exact global_step_range S_pos K_pos R_pos Q_pos sigma_mem cert220 hud hu220 t ⟨ht220,hstop220⟩
  have h220 := global_step_endpoint S_pos K_pos R_pos Q_pos sigma_mem cert220 hud hu220
  have hu221 := join_bound Q_pos join221 h220
  have ht221 : startTime R step221 ≤ t := by
    rw [start_eq_stop join221.1]
    exact (lt_of_not_ge hstop220).le
  by_cases hstop221 : t ≤ stopTime R step221
  · exact global_step_range S_pos K_pos R_pos Q_pos sigma_mem cert221 hud hu221 t ⟨ht221,hstop221⟩
  have h221 := global_step_endpoint S_pos K_pos R_pos Q_pos sigma_mem cert221 hud hu221
  have hu222 := join_bound Q_pos join222 h221
  have ht222 : startTime R step222 ≤ t := by
    rw [start_eq_stop join222.1]
    exact (lt_of_not_ge hstop221).le
  by_cases hstop222 : t ≤ stopTime R step222
  · exact global_step_range S_pos K_pos R_pos Q_pos sigma_mem cert222 hud hu222 t ⟨ht222,hstop222⟩
  have h222 := global_step_endpoint S_pos K_pos R_pos Q_pos sigma_mem cert222 hud hu222
  have hu223 := join_bound Q_pos join223 h222
  have ht223 : startTime R step223 ≤ t := by
    rw [start_eq_stop join223.1]
    exact (lt_of_not_ge hstop222).le
  exact global_step_range S_pos K_pos R_pos Q_pos sigma_mem cert223 hud hu223 t ⟨ht223,ht.2⟩
theorem range_224 {u : ℝ → ℝ} (hud : ∀ t ∈ Icc (0:ℝ) (9/100), HasDerivWithinAt u
    (globalField (SN/S) (KN/K) t (u t)) (Icc 0 (9/100)) t)
    (hu : u (startTime R step224) ∈ Icc ((head step224.lo:ℝ)/Q) ((head step224.hi:ℝ)/Q)) :
    ∀ t ∈ Icc (startTime R step224) (stopTime R step231), u t ∈ Icc (0:ℝ) (999/1000) := by
  intro t ht
  have ht224 := ht.1
  by_cases hstop224 : t ≤ stopTime R step224
  · exact global_step_range S_pos K_pos R_pos Q_pos sigma_mem cert224 hud hu t ⟨ht224,hstop224⟩
  have h224 := global_step_endpoint S_pos K_pos R_pos Q_pos sigma_mem cert224 hud hu
  have hu225 := join_bound Q_pos join225 h224
  have ht225 : startTime R step225 ≤ t := by
    rw [start_eq_stop join225.1]
    exact (lt_of_not_ge hstop224).le
  by_cases hstop225 : t ≤ stopTime R step225
  · exact global_step_range S_pos K_pos R_pos Q_pos sigma_mem cert225 hud hu225 t ⟨ht225,hstop225⟩
  have h225 := global_step_endpoint S_pos K_pos R_pos Q_pos sigma_mem cert225 hud hu225
  have hu226 := join_bound Q_pos join226 h225
  have ht226 : startTime R step226 ≤ t := by
    rw [start_eq_stop join226.1]
    exact (lt_of_not_ge hstop225).le
  by_cases hstop226 : t ≤ stopTime R step226
  · exact global_step_range S_pos K_pos R_pos Q_pos sigma_mem cert226 hud hu226 t ⟨ht226,hstop226⟩
  have h226 := global_step_endpoint S_pos K_pos R_pos Q_pos sigma_mem cert226 hud hu226
  have hu227 := join_bound Q_pos join227 h226
  have ht227 : startTime R step227 ≤ t := by
    rw [start_eq_stop join227.1]
    exact (lt_of_not_ge hstop226).le
  by_cases hstop227 : t ≤ stopTime R step227
  · exact global_step_range S_pos K_pos R_pos Q_pos sigma_mem cert227 hud hu227 t ⟨ht227,hstop227⟩
  have h227 := global_step_endpoint S_pos K_pos R_pos Q_pos sigma_mem cert227 hud hu227
  have hu228 := join_bound Q_pos join228 h227
  have ht228 : startTime R step228 ≤ t := by
    rw [start_eq_stop join228.1]
    exact (lt_of_not_ge hstop227).le
  by_cases hstop228 : t ≤ stopTime R step228
  · exact global_step_range S_pos K_pos R_pos Q_pos sigma_mem cert228 hud hu228 t ⟨ht228,hstop228⟩
  have h228 := global_step_endpoint S_pos K_pos R_pos Q_pos sigma_mem cert228 hud hu228
  have hu229 := join_bound Q_pos join229 h228
  have ht229 : startTime R step229 ≤ t := by
    rw [start_eq_stop join229.1]
    exact (lt_of_not_ge hstop228).le
  by_cases hstop229 : t ≤ stopTime R step229
  · exact global_step_range S_pos K_pos R_pos Q_pos sigma_mem cert229 hud hu229 t ⟨ht229,hstop229⟩
  have h229 := global_step_endpoint S_pos K_pos R_pos Q_pos sigma_mem cert229 hud hu229
  have hu230 := join_bound Q_pos join230 h229
  have ht230 : startTime R step230 ≤ t := by
    rw [start_eq_stop join230.1]
    exact (lt_of_not_ge hstop229).le
  by_cases hstop230 : t ≤ stopTime R step230
  · exact global_step_range S_pos K_pos R_pos Q_pos sigma_mem cert230 hud hu230 t ⟨ht230,hstop230⟩
  have h230 := global_step_endpoint S_pos K_pos R_pos Q_pos sigma_mem cert230 hud hu230
  have hu231 := join_bound Q_pos join231 h230
  have ht231 : startTime R step231 ≤ t := by
    rw [start_eq_stop join231.1]
    exact (lt_of_not_ge hstop230).le
  exact global_step_range S_pos K_pos R_pos Q_pos sigma_mem cert231 hud hu231 t ⟨ht231,ht.2⟩
theorem full_range {u : ℝ → ℝ} (hud : ∀ t ∈ Icc (0:ℝ) (9/100), HasDerivWithinAt u
    (globalField (SN/S) (KN/K) t (u t)) (Icc 0 (9/100)) t)
    (hu : u 0 ∈ Icc ((head step0.lo:ℝ)/Q) ((head step0.hi:ℝ)/Q)) :
    ∀ t ∈ Icc (0:ℝ) (9/100), u t ∈ Icc (0:ℝ) (999/1000) := by
  intro t ht
  have hu0 : u (startTime R step0) ∈ Icc ((head step0.lo:ℝ)/Q) ((head step0.hi:ℝ)/Q) := first_time.symm ▸ hu
  have ht0 : startTime R step0 ≤ t := first_time.symm ▸ ht.1
  by_cases hstop0 : t ≤ stopTime R step15
  · exact range_0 hud hu0 t ⟨ht0,hstop0⟩
  have h0 := propagate_0 hud hu0
  have hu16 := join_bound Q_pos join16 h0
  have ht16 : startTime R step16 ≤ t := by
    rw [start_eq_stop join16.1]
    exact (lt_of_not_ge hstop0).le
  by_cases hstop16 : t ≤ stopTime R step31
  · exact range_16 hud hu16 t ⟨ht16,hstop16⟩
  have h16 := propagate_16 hud hu16
  have hu32 := join_bound Q_pos join32 h16
  have ht32 : startTime R step32 ≤ t := by
    rw [start_eq_stop join32.1]
    exact (lt_of_not_ge hstop16).le
  by_cases hstop32 : t ≤ stopTime R step47
  · exact range_32 hud hu32 t ⟨ht32,hstop32⟩
  have h32 := propagate_32 hud hu32
  have hu48 := join_bound Q_pos join48 h32
  have ht48 : startTime R step48 ≤ t := by
    rw [start_eq_stop join48.1]
    exact (lt_of_not_ge hstop32).le
  by_cases hstop48 : t ≤ stopTime R step63
  · exact range_48 hud hu48 t ⟨ht48,hstop48⟩
  have h48 := propagate_48 hud hu48
  have hu64 := join_bound Q_pos join64 h48
  have ht64 : startTime R step64 ≤ t := by
    rw [start_eq_stop join64.1]
    exact (lt_of_not_ge hstop48).le
  by_cases hstop64 : t ≤ stopTime R step79
  · exact range_64 hud hu64 t ⟨ht64,hstop64⟩
  have h64 := propagate_64 hud hu64
  have hu80 := join_bound Q_pos join80 h64
  have ht80 : startTime R step80 ≤ t := by
    rw [start_eq_stop join80.1]
    exact (lt_of_not_ge hstop64).le
  by_cases hstop80 : t ≤ stopTime R step95
  · exact range_80 hud hu80 t ⟨ht80,hstop80⟩
  have h80 := propagate_80 hud hu80
  have hu96 := join_bound Q_pos join96 h80
  have ht96 : startTime R step96 ≤ t := by
    rw [start_eq_stop join96.1]
    exact (lt_of_not_ge hstop80).le
  by_cases hstop96 : t ≤ stopTime R step111
  · exact range_96 hud hu96 t ⟨ht96,hstop96⟩
  have h96 := propagate_96 hud hu96
  have hu112 := join_bound Q_pos join112 h96
  have ht112 : startTime R step112 ≤ t := by
    rw [start_eq_stop join112.1]
    exact (lt_of_not_ge hstop96).le
  by_cases hstop112 : t ≤ stopTime R step127
  · exact range_112 hud hu112 t ⟨ht112,hstop112⟩
  have h112 := propagate_112 hud hu112
  have hu128 := join_bound Q_pos join128 h112
  have ht128 : startTime R step128 ≤ t := by
    rw [start_eq_stop join128.1]
    exact (lt_of_not_ge hstop112).le
  by_cases hstop128 : t ≤ stopTime R step143
  · exact range_128 hud hu128 t ⟨ht128,hstop128⟩
  have h128 := propagate_128 hud hu128
  have hu144 := join_bound Q_pos join144 h128
  have ht144 : startTime R step144 ≤ t := by
    rw [start_eq_stop join144.1]
    exact (lt_of_not_ge hstop128).le
  by_cases hstop144 : t ≤ stopTime R step159
  · exact range_144 hud hu144 t ⟨ht144,hstop144⟩
  have h144 := propagate_144 hud hu144
  have hu160 := join_bound Q_pos join160 h144
  have ht160 : startTime R step160 ≤ t := by
    rw [start_eq_stop join160.1]
    exact (lt_of_not_ge hstop144).le
  by_cases hstop160 : t ≤ stopTime R step175
  · exact range_160 hud hu160 t ⟨ht160,hstop160⟩
  have h160 := propagate_160 hud hu160
  have hu176 := join_bound Q_pos join176 h160
  have ht176 : startTime R step176 ≤ t := by
    rw [start_eq_stop join176.1]
    exact (lt_of_not_ge hstop160).le
  by_cases hstop176 : t ≤ stopTime R step191
  · exact range_176 hud hu176 t ⟨ht176,hstop176⟩
  have h176 := propagate_176 hud hu176
  have hu192 := join_bound Q_pos join192 h176
  have ht192 : startTime R step192 ≤ t := by
    rw [start_eq_stop join192.1]
    exact (lt_of_not_ge hstop176).le
  by_cases hstop192 : t ≤ stopTime R step207
  · exact range_192 hud hu192 t ⟨ht192,hstop192⟩
  have h192 := propagate_192 hud hu192
  have hu208 := join_bound Q_pos join208 h192
  have ht208 : startTime R step208 ≤ t := by
    rw [start_eq_stop join208.1]
    exact (lt_of_not_ge hstop192).le
  by_cases hstop208 : t ≤ stopTime R step223
  · exact range_208 hud hu208 t ⟨ht208,hstop208⟩
  have h208 := propagate_208 hud hu208
  have hu224 := join_bound Q_pos join224 h208
  have ht224 : startTime R step224 ≤ t := by
    rw [start_eq_stop join224.1]
    exact (lt_of_not_ge hstop208).le
  exact range_224 hud hu224 t ⟨ht224,last_time.symm ▸ ht.2⟩
theorem exists_actual_regular (u0 : ℝ)
    (hu0 : u0 ∈ Icc ((head step0.lo:ℝ)/Q) ((head step0.hi:ℝ)/Q)) :
    ∃ u : ℝ → ℝ, u 0=u0 ∧ ContinuousOn u (Icc (0:ℝ) (9/100)) ∧
      (∀ t ∈ Icc (0:ℝ) (9/100), u t ∈ Icc (0:ℝ) (999/1000)) ∧
      (∀ t ∈ Icc (0:ℝ) (9/100), HasDerivWithinAt u
        (-numer (KN/K) (99/100-t) (u t)/denom (SN/S) (99/100-t) (u t)) (Icc 0 (9/100)) t) ∧
      u (9/100)<673/1000 := by
  obtain ⟨u,hu,huc,hud⟩ := exists_global_clamped_solution (SN/S) (KN/K) sigma_mem u0
  have he : u 0 ∈ Icc ((head step0.lo:ℝ)/Q) ((head step0.hi:ℝ)/Q) := hu.symm ▸ hu0
  have hr := full_range hud he
  exact ⟨u,hu,huc,hr,unclamped_derivative hud hr,endpoint_bound hud he⟩
end SepticProfile.RegularLowData


end

end OAI
