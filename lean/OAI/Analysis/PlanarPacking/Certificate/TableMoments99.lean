import OAI.Analysis.PlanarPacking.Certificate.TableDensityValues
import OAI.Analysis.PlanarPacking.TableRuleBridge
import OAI.Analysis.PlanarPacking.Certificate.AtomKernels
import OAI.Analysis.PlanarPacking.Certificate.KernelValues100

namespace OAI

/-!
# Finite interval certificates for the planar Fourier construction

These rational enclosures certify the numerical bounds in the sharp planar
Fourier construction of OpenAI. All interval endpoints are exact integers.
-/

namespace SharpPlanar.CachedData
open IntegerIntervals IntegerBasis IntegerGrid Numerical
namespace tm0_99_0
noncomputable def chunk (j : Fin 6) (i : Fin 16) : CBox := finSum (fun k => (density0 j i k).mul (kernel99_0 j i k))
noncomputable def s0_0 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
lemma c0_0 : chunk 0 0 = s0_0 := by decide +kernel
noncomputable def s0_1 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
lemma c0_1 : chunk 0 1 = s0_1 := by decide +kernel
noncomputable def s0_2 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
lemma c0_2 : chunk 0 2 = s0_2 := by decide +kernel
noncomputable def s0_3 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
lemma c0_3 : chunk 0 3 = s0_3 := by decide +kernel
noncomputable def s0_4 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
lemma c0_4 : chunk 0 4 = s0_4 := by decide +kernel
noncomputable def s0_5 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
lemma c0_5 : chunk 0 5 = s0_5 := by decide +kernel
noncomputable def s0_6 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
lemma c0_6 : chunk 0 6 = s0_6 := by decide +kernel
noncomputable def s0_7 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
lemma c0_7 : chunk 0 7 = s0_7 := by decide +kernel
noncomputable def s0_8 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
lemma c0_8 : chunk 0 8 = s0_8 := by decide +kernel
noncomputable def s0_9 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
lemma c0_9 : chunk 0 9 = s0_9 := by decide +kernel
noncomputable def s0_10 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
lemma c0_10 : chunk 0 10 = s0_10 := by decide +kernel
noncomputable def s0_11 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
lemma c0_11 : chunk 0 11 = s0_11 := by decide +kernel
noncomputable def s0_12 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
lemma c0_12 : chunk 0 12 = s0_12 := by decide +kernel
noncomputable def s0_13 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
lemma c0_13 : chunk 0 13 = s0_13 := by decide +kernel
noncomputable def s0_14 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
lemma c0_14 : chunk 0 14 = s0_14 := by decide +kernel
noncomputable def s0_15 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
lemma c0_15 : chunk 0 15 = s0_15 := by decide +kernel
noncomputable def s0 : Fin 16 → CBox := ![s0_0,s0_1,s0_2,s0_3,s0_4,s0_5,s0_6,s0_7,s0_8,s0_9,s0_10,s0_11,s0_12,s0_13,s0_14,s0_15]
lemma s0_eq (i : Fin 16) : chunk 0 i = s0 i := by
  fin_cases i
  · exact c0_0
  · exact c0_1
  · exact c0_2
  · exact c0_3
  · exact c0_4
  · exact c0_5
  · exact c0_6
  · exact c0_7
  · exact c0_8
  · exact c0_9
  · exact c0_10
  · exact c0_11
  · exact c0_12
  · exact c0_13
  · exact c0_14
  · exact c0_15
noncomputable def s1_0 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
lemma c1_0 : chunk 1 0 = s1_0 := by decide +kernel
noncomputable def s1_1 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
lemma c1_1 : chunk 1 1 = s1_1 := by decide +kernel
noncomputable def s1_2 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
lemma c1_2 : chunk 1 2 = s1_2 := by decide +kernel
noncomputable def s1_3 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
lemma c1_3 : chunk 1 3 = s1_3 := by decide +kernel
noncomputable def s1_4 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
lemma c1_4 : chunk 1 4 = s1_4 := by decide +kernel
noncomputable def s1_5 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
lemma c1_5 : chunk 1 5 = s1_5 := by decide +kernel
noncomputable def s1_6 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
lemma c1_6 : chunk 1 6 = s1_6 := by decide +kernel
noncomputable def s1_7 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
lemma c1_7 : chunk 1 7 = s1_7 := by decide +kernel
noncomputable def s1_8 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
lemma c1_8 : chunk 1 8 = s1_8 := by decide +kernel
noncomputable def s1_9 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
lemma c1_9 : chunk 1 9 = s1_9 := by decide +kernel
noncomputable def s1_10 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
lemma c1_10 : chunk 1 10 = s1_10 := by decide +kernel
noncomputable def s1_11 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
lemma c1_11 : chunk 1 11 = s1_11 := by decide +kernel
noncomputable def s1_12 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
lemma c1_12 : chunk 1 12 = s1_12 := by decide +kernel
noncomputable def s1_13 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
lemma c1_13 : chunk 1 13 = s1_13 := by decide +kernel
noncomputable def s1_14 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
lemma c1_14 : chunk 1 14 = s1_14 := by decide +kernel
noncomputable def s1_15 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
lemma c1_15 : chunk 1 15 = s1_15 := by decide +kernel
noncomputable def s1 : Fin 16 → CBox := ![s1_0,s1_1,s1_2,s1_3,s1_4,s1_5,s1_6,s1_7,s1_8,s1_9,s1_10,s1_11,s1_12,s1_13,s1_14,s1_15]
lemma s1_eq (i : Fin 16) : chunk 1 i = s1 i := by
  fin_cases i
  · exact c1_0
  · exact c1_1
  · exact c1_2
  · exact c1_3
  · exact c1_4
  · exact c1_5
  · exact c1_6
  · exact c1_7
  · exact c1_8
  · exact c1_9
  · exact c1_10
  · exact c1_11
  · exact c1_12
  · exact c1_13
  · exact c1_14
  · exact c1_15
noncomputable def s2_0 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
lemma c2_0 : chunk 2 0 = s2_0 := by decide +kernel
noncomputable def s2_1 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
lemma c2_1 : chunk 2 1 = s2_1 := by decide +kernel
noncomputable def s2_2 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
lemma c2_2 : chunk 2 2 = s2_2 := by decide +kernel
noncomputable def s2_3 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
lemma c2_3 : chunk 2 3 = s2_3 := by decide +kernel
noncomputable def s2_4 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
lemma c2_4 : chunk 2 4 = s2_4 := by decide +kernel
noncomputable def s2_5 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
lemma c2_5 : chunk 2 5 = s2_5 := by decide +kernel
noncomputable def s2_6 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
lemma c2_6 : chunk 2 6 = s2_6 := by decide +kernel
noncomputable def s2_7 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
lemma c2_7 : chunk 2 7 = s2_7 := by decide +kernel
noncomputable def s2_8 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
lemma c2_8 : chunk 2 8 = s2_8 := by decide +kernel
noncomputable def s2_9 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
lemma c2_9 : chunk 2 9 = s2_9 := by decide +kernel
noncomputable def s2_10 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
lemma c2_10 : chunk 2 10 = s2_10 := by decide +kernel
noncomputable def s2_11 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
lemma c2_11 : chunk 2 11 = s2_11 := by decide +kernel
noncomputable def s2_12 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
lemma c2_12 : chunk 2 12 = s2_12 := by decide +kernel
noncomputable def s2_13 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
lemma c2_13 : chunk 2 13 = s2_13 := by decide +kernel
noncomputable def s2_14 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
lemma c2_14 : chunk 2 14 = s2_14 := by decide +kernel
noncomputable def s2_15 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
lemma c2_15 : chunk 2 15 = s2_15 := by decide +kernel
noncomputable def s2 : Fin 16 → CBox := ![s2_0,s2_1,s2_2,s2_3,s2_4,s2_5,s2_6,s2_7,s2_8,s2_9,s2_10,s2_11,s2_12,s2_13,s2_14,s2_15]
lemma s2_eq (i : Fin 16) : chunk 2 i = s2 i := by
  fin_cases i
  · exact c2_0
  · exact c2_1
  · exact c2_2
  · exact c2_3
  · exact c2_4
  · exact c2_5
  · exact c2_6
  · exact c2_7
  · exact c2_8
  · exact c2_9
  · exact c2_10
  · exact c2_11
  · exact c2_12
  · exact c2_13
  · exact c2_14
  · exact c2_15
noncomputable def s3_0 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
lemma c3_0 : chunk 3 0 = s3_0 := by decide +kernel
noncomputable def s3_1 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
lemma c3_1 : chunk 3 1 = s3_1 := by decide +kernel
noncomputable def s3_2 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
lemma c3_2 : chunk 3 2 = s3_2 := by decide +kernel
noncomputable def s3_3 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
lemma c3_3 : chunk 3 3 = s3_3 := by decide +kernel
noncomputable def s3_4 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
lemma c3_4 : chunk 3 4 = s3_4 := by decide +kernel
noncomputable def s3_5 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
lemma c3_5 : chunk 3 5 = s3_5 := by decide +kernel
noncomputable def s3_6 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
lemma c3_6 : chunk 3 6 = s3_6 := by decide +kernel
noncomputable def s3_7 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
lemma c3_7 : chunk 3 7 = s3_7 := by decide +kernel
noncomputable def s3_8 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
lemma c3_8 : chunk 3 8 = s3_8 := by decide +kernel
noncomputable def s3_9 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
lemma c3_9 : chunk 3 9 = s3_9 := by decide +kernel
noncomputable def s3_10 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
lemma c3_10 : chunk 3 10 = s3_10 := by decide +kernel
noncomputable def s3_11 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
lemma c3_11 : chunk 3 11 = s3_11 := by decide +kernel
noncomputable def s3_12 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
lemma c3_12 : chunk 3 12 = s3_12 := by decide +kernel
noncomputable def s3_13 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
lemma c3_13 : chunk 3 13 = s3_13 := by decide +kernel
noncomputable def s3_14 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
lemma c3_14 : chunk 3 14 = s3_14 := by decide +kernel
noncomputable def s3_15 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
lemma c3_15 : chunk 3 15 = s3_15 := by decide +kernel
noncomputable def s3 : Fin 16 → CBox := ![s3_0,s3_1,s3_2,s3_3,s3_4,s3_5,s3_6,s3_7,s3_8,s3_9,s3_10,s3_11,s3_12,s3_13,s3_14,s3_15]
lemma s3_eq (i : Fin 16) : chunk 3 i = s3 i := by
  fin_cases i
  · exact c3_0
  · exact c3_1
  · exact c3_2
  · exact c3_3
  · exact c3_4
  · exact c3_5
  · exact c3_6
  · exact c3_7
  · exact c3_8
  · exact c3_9
  · exact c3_10
  · exact c3_11
  · exact c3_12
  · exact c3_13
  · exact c3_14
  · exact c3_15
noncomputable def s4_0 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
lemma c4_0 : chunk 4 0 = s4_0 := by decide +kernel
noncomputable def s4_1 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
lemma c4_1 : chunk 4 1 = s4_1 := by decide +kernel
noncomputable def s4_2 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
lemma c4_2 : chunk 4 2 = s4_2 := by decide +kernel
noncomputable def s4_3 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
lemma c4_3 : chunk 4 3 = s4_3 := by decide +kernel
noncomputable def s4_4 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
lemma c4_4 : chunk 4 4 = s4_4 := by decide +kernel
noncomputable def s4_5 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
lemma c4_5 : chunk 4 5 = s4_5 := by decide +kernel
noncomputable def s4_6 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
lemma c4_6 : chunk 4 6 = s4_6 := by decide +kernel
noncomputable def s4_7 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
lemma c4_7 : chunk 4 7 = s4_7 := by decide +kernel
noncomputable def s4_8 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
lemma c4_8 : chunk 4 8 = s4_8 := by decide +kernel
noncomputable def s4_9 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
lemma c4_9 : chunk 4 9 = s4_9 := by decide +kernel
noncomputable def s4_10 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
lemma c4_10 : chunk 4 10 = s4_10 := by decide +kernel
noncomputable def s4_11 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
lemma c4_11 : chunk 4 11 = s4_11 := by decide +kernel
noncomputable def s4_12 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
lemma c4_12 : chunk 4 12 = s4_12 := by decide +kernel
noncomputable def s4_13 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
lemma c4_13 : chunk 4 13 = s4_13 := by decide +kernel
noncomputable def s4_14 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
lemma c4_14 : chunk 4 14 = s4_14 := by decide +kernel
noncomputable def s4_15 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
lemma c4_15 : chunk 4 15 = s4_15 := by decide +kernel
noncomputable def s4 : Fin 16 → CBox := ![s4_0,s4_1,s4_2,s4_3,s4_4,s4_5,s4_6,s4_7,s4_8,s4_9,s4_10,s4_11,s4_12,s4_13,s4_14,s4_15]
lemma s4_eq (i : Fin 16) : chunk 4 i = s4 i := by
  fin_cases i
  · exact c4_0
  · exact c4_1
  · exact c4_2
  · exact c4_3
  · exact c4_4
  · exact c4_5
  · exact c4_6
  · exact c4_7
  · exact c4_8
  · exact c4_9
  · exact c4_10
  · exact c4_11
  · exact c4_12
  · exact c4_13
  · exact c4_14
  · exact c4_15
noncomputable def s5_0 : CBox := ⟨⟨56002351629753822433,56002381749727145659⟩,⟨3580664185323347443,3580694305296670662⟩⟩
lemma c5_0 : chunk 5 0 = s5_0 := by decide +kernel
noncomputable def s5_1 : CBox := ⟨⟨57817034443160071720,57817092103660395505⟩,⟨(-48431802000282268207),(-48431744339781944426)⟩⟩
lemma c5_1 : chunk 5 1 = s5_1 := by decide +kernel
noncomputable def s5_2 : CBox := ⟨⟨(-15528225975911660410),(-15528187743462859279)⟩,⟨(-21140042517911504257),(-21140004285462703127)⟩⟩
lemma c5_2 : chunk 5 2 = s5_2 := by decide +kernel
noncomputable def s5_3 : CBox := ⟨⟨(-1077415895664683825),(-1077403180376235466)⟩,⟨3657340217123234768,3657352932411683127⟩⟩
lemma c5_3 : chunk 5 3 = s5_3 := by decide +kernel
noncomputable def s5_4 : CBox := ⟨⟨138357350742763553,138359591681561692⟩,⟨(-230001870687564974),(-229999629748766837)⟩⟩
lemma c5_4 : chunk 5 4 = s5_4 := by decide +kernel
noncomputable def s5_5 : CBox := ⟨⟨(-1933453524169397),(-1933249311325800)⟩,⟨9590541349128604,9590745561972204⟩⟩
lemma c5_5 : chunk 5 5 = s5_5 := by decide +kernel
noncomputable def s5_6 : CBox := ⟨⟨(-119154367436466),(-119144817852409)⟩,⟨(-154788434995685),(-154778885411630)⟩⟩
lemma c5_6 : chunk 5 6 = s5_6 := by decide +kernel
noncomputable def s5_7 : CBox := ⟨⟨2210800425695,2211038910412⟩,⟨(-778354761380),(-778116276663)⟩⟩
lemma c5_7 : chunk 5 7 = s5_7 := by decide +kernel
noncomputable def s5_8 : CBox := ⟨⟨5179576552,5183005561⟩,⟨18661017518,18664446531⟩⟩
lemma c5_8 : chunk 5 8 = s5_8 := by decide +kernel
noncomputable def s5_9 : CBox := ⟨⟨(-125786334),(-125754114)⟩,⟨35864619,35896839⟩⟩
lemma c5_9 : chunk 5 9 = s5_9 := by decide +kernel
noncomputable def s5_10 : CBox := ⟨⟨(-148226),(-147965)⟩,⟨(-869055),(-868797)⟩⟩
lemma c5_10 : chunk 5 10 = s5_10 := by decide +kernel
noncomputable def s5_11 : CBox := ⟨⟨7157,7174⟩,⟨1847,1866⟩⟩
lemma c5_11 : chunk 5 11 = s5_11 := by decide +kernel
noncomputable def s5_12 : CBox := ⟨⟨(-101),(-84)⟩,⟨28,44⟩⟩
lemma c5_12 : chunk 5 12 = s5_12 := by decide +kernel
noncomputable def s5_13 : CBox := ⟨⟨(-6),16⟩,⟨(-14),2⟩⟩
lemma c5_13 : chunk 5 13 = s5_13 := by decide +kernel
noncomputable def s5_14 : CBox := ⟨⟨(-16),16⟩,⟨(-16),14⟩⟩
lemma c5_14 : chunk 5 14 = s5_14 := by decide +kernel
noncomputable def s5_15 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
lemma c5_15 : chunk 5 15 = s5_15 := by decide +kernel
noncomputable def s5 : Fin 16 → CBox := ![s5_0,s5_1,s5_2,s5_3,s5_4,s5_5,s5_6,s5_7,s5_8,s5_9,s5_10,s5_11,s5_12,s5_13,s5_14,s5_15]
lemma s5_eq (i : Fin 16) : chunk 5 i = s5 i := by
  fin_cases i
  · exact c5_0
  · exact c5_1
  · exact c5_2
  · exact c5_3
  · exact c5_4
  · exact c5_5
  · exact c5_6
  · exact c5_7
  · exact c5_8
  · exact c5_9
  · exact c5_10
  · exact c5_11
  · exact c5_12
  · exact c5_13
  · exact c5_14
  · exact c5_15
noncomputable def sums : Fin 6 → Fin 16 → CBox := ![s0,s1,s2,s3,s4,s5]
lemma sums_eq (j : Fin 6) (i : Fin 16) : chunk j i = sums j i := by
  fin_cases j
  · exact s0_eq i
  · exact s1_eq i
  · exact s2_eq i
  · exact s3_eq i
  · exact s4_eq i
  · exact s5_eq i
noncomputable def ans : CBox := ⟨⟨16225008526673796837,16225032057199475371⟩,⟨(-10425734498863228345),(-10425710968337549814)⟩⟩
lemma checked : cachedMomentRuleBox density0 kernel99_0 = ans := by
  change (finSum (fun j => (finSum (fun i => chunk j i)).scale 1 6)) = ans
  simp_rw [sums_eq]
  decide +kernel
lemma contains : ans.Contains (tableMomentRule false 99 0) := by
  rw [← checked]
  simpa only [Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Bool.false_eq_true,ite_false,ite_true] using @tableRule_contains_bridge false 99 false density0 kernel99_0
    density0_contains kernel99_0_contains
noncomputable def atomAnswer : CBox := ⟨⟨62679313250272488329,62679313250272494141⟩,⟨(-226937335747300982081),(-226937335747300976268)⟩⟩
lemma atomChecked : tableAtomBox false atomKernel99_0 = atomAnswer := by decide +kernel
lemma atomContains : atomAnswer.Contains (tableMomentAtom false 99 0) := by
  rw [← atomChecked]
  exact tableAtomBox_contains false atomKernel99_0_contains
noncomputable def realAnswer : RBox := ⟨78904321776846285166,78904345307571969512⟩
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
lemma KContains : realAnswer.Contains (tableMomentK false 99 0) := by
  rw [← realChecked]
  exact tableMomentK_contains atomContains contains (by norm_num) (by norm_num)
end tm0_99_0

namespace tm0_99_1
noncomputable def chunk (j : Fin 6) (i : Fin 16) : CBox := finSum (fun k => (density0 j i k).mul (kernel99_1 j i k))
noncomputable def s0_0 : CBox := ⟨⟨(-17),17⟩,⟨(-17),17⟩⟩
lemma c0_0 : chunk 0 0 = s0_0 := by decide +kernel
noncomputable def s0_1 : CBox := ⟨⟨(-33),33⟩,⟨(-33),33⟩⟩
lemma c0_1 : chunk 0 1 = s0_1 := by decide +kernel
noncomputable def s0_2 : CBox := ⟨⟨(-48),48⟩,⟨(-48),48⟩⟩
lemma c0_2 : chunk 0 2 = s0_2 := by decide +kernel
noncomputable def s0_3 : CBox := ⟨⟨(-63),63⟩,⟨(-63),63⟩⟩
lemma c0_3 : chunk 0 3 = s0_3 := by decide +kernel
noncomputable def s0_4 : CBox := ⟨⟨(-75),75⟩,⟨(-75),75⟩⟩
lemma c0_4 : chunk 0 4 = s0_4 := by decide +kernel
noncomputable def s0_5 : CBox := ⟨⟨(-80),80⟩,⟨(-80),80⟩⟩
lemma c0_5 : chunk 0 5 = s0_5 := by decide +kernel
noncomputable def s0_6 : CBox := ⟨⟨(-88),88⟩,⟨(-88),88⟩⟩
lemma c0_6 : chunk 0 6 = s0_6 := by decide +kernel
noncomputable def s0_7 : CBox := ⟨⟨(-96),96⟩,⟨(-96),96⟩⟩
lemma c0_7 : chunk 0 7 = s0_7 := by decide +kernel
noncomputable def s0_8 : CBox := ⟨⟨(-89),89⟩,⟨(-89),89⟩⟩
lemma c0_8 : chunk 0 8 = s0_8 := by decide +kernel
noncomputable def s0_9 : CBox := ⟨⟨(-80),80⟩,⟨(-80),80⟩⟩
lemma c0_9 : chunk 0 9 = s0_9 := by decide +kernel
noncomputable def s0_10 : CBox := ⟨⟨(-74),74⟩,⟨(-74),74⟩⟩
lemma c0_10 : chunk 0 10 = s0_10 := by decide +kernel
noncomputable def s0_11 : CBox := ⟨⟨(-64),64⟩,⟨(-64),64⟩⟩
lemma c0_11 : chunk 0 11 = s0_11 := by decide +kernel
noncomputable def s0_12 : CBox := ⟨⟨(-47),47⟩,⟨(-47),47⟩⟩
lemma c0_12 : chunk 0 12 = s0_12 := by decide +kernel
noncomputable def s0_13 : CBox := ⟨⟨(-32),32⟩,⟨(-32),32⟩⟩
lemma c0_13 : chunk 0 13 = s0_13 := by decide +kernel
noncomputable def s0_14 : CBox := ⟨⟨(-21),21⟩,⟨(-21),21⟩⟩
lemma c0_14 : chunk 0 14 = s0_14 := by decide +kernel
noncomputable def s0_15 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
lemma c0_15 : chunk 0 15 = s0_15 := by decide +kernel
noncomputable def s0 : Fin 16 → CBox := ![s0_0,s0_1,s0_2,s0_3,s0_4,s0_5,s0_6,s0_7,s0_8,s0_9,s0_10,s0_11,s0_12,s0_13,s0_14,s0_15]
lemma s0_eq (i : Fin 16) : chunk 0 i = s0 i := by
  fin_cases i
  · exact c0_0
  · exact c0_1
  · exact c0_2
  · exact c0_3
  · exact c0_4
  · exact c0_5
  · exact c0_6
  · exact c0_7
  · exact c0_8
  · exact c0_9
  · exact c0_10
  · exact c0_11
  · exact c0_12
  · exact c0_13
  · exact c0_14
  · exact c0_15
noncomputable def s1_0 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
lemma c1_0 : chunk 1 0 = s1_0 := by decide +kernel
noncomputable def s1_1 : CBox := ⟨⟨(-28),28⟩,⟨(-28),28⟩⟩
lemma c1_1 : chunk 1 1 = s1_1 := by decide +kernel
noncomputable def s1_2 : CBox := ⟨⟨(-38),38⟩,⟨(-38),38⟩⟩
lemma c1_2 : chunk 1 2 = s1_2 := by decide +kernel
noncomputable def s1_3 : CBox := ⟨⟨(-48),48⟩,⟨(-48),48⟩⟩
lemma c1_3 : chunk 1 3 = s1_3 := by decide +kernel
noncomputable def s1_4 : CBox := ⟨⟨(-63),63⟩,⟨(-63),63⟩⟩
lemma c1_4 : chunk 1 4 = s1_4 := by decide +kernel
noncomputable def s1_5 : CBox := ⟨⟨(-65),65⟩,⟨(-65),65⟩⟩
lemma c1_5 : chunk 1 5 = s1_5 := by decide +kernel
noncomputable def s1_6 : CBox := ⟨⟨(-80),80⟩,⟨(-80),80⟩⟩
lemma c1_6 : chunk 1 6 = s1_6 := by decide +kernel
noncomputable def s1_7 : CBox := ⟨⟨(-80),80⟩,⟨(-80),80⟩⟩
lemma c1_7 : chunk 1 7 = s1_7 := by decide +kernel
noncomputable def s1_8 : CBox := ⟨⟨(-80),80⟩,⟨(-80),80⟩⟩
lemma c1_8 : chunk 1 8 = s1_8 := by decide +kernel
noncomputable def s1_9 : CBox := ⟨⟨(-80),80⟩,⟨(-80),80⟩⟩
lemma c1_9 : chunk 1 9 = s1_9 := by decide +kernel
noncomputable def s1_10 : CBox := ⟨⟨(-79),79⟩,⟨(-79),79⟩⟩
lemma c1_10 : chunk 1 10 = s1_10 := by decide +kernel
noncomputable def s1_11 : CBox := ⟨⟨(-64),64⟩,⟨(-64),64⟩⟩
lemma c1_11 : chunk 1 11 = s1_11 := by decide +kernel
noncomputable def s1_12 : CBox := ⟨⟨(-56),56⟩,⟨(-56),56⟩⟩
lemma c1_12 : chunk 1 12 = s1_12 := by decide +kernel
noncomputable def s1_13 : CBox := ⟨⟨(-45),45⟩,⟨(-45),45⟩⟩
lemma c1_13 : chunk 1 13 = s1_13 := by decide +kernel
noncomputable def s1_14 : CBox := ⟨⟨(-31),31⟩,⟨(-31),31⟩⟩
lemma c1_14 : chunk 1 14 = s1_14 := by decide +kernel
noncomputable def s1_15 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
lemma c1_15 : chunk 1 15 = s1_15 := by decide +kernel
noncomputable def s1 : Fin 16 → CBox := ![s1_0,s1_1,s1_2,s1_3,s1_4,s1_5,s1_6,s1_7,s1_8,s1_9,s1_10,s1_11,s1_12,s1_13,s1_14,s1_15]
lemma s1_eq (i : Fin 16) : chunk 1 i = s1 i := by
  fin_cases i
  · exact c1_0
  · exact c1_1
  · exact c1_2
  · exact c1_3
  · exact c1_4
  · exact c1_5
  · exact c1_6
  · exact c1_7
  · exact c1_8
  · exact c1_9
  · exact c1_10
  · exact c1_11
  · exact c1_12
  · exact c1_13
  · exact c1_14
  · exact c1_15
noncomputable def s2_0 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
lemma c2_0 : chunk 2 0 = s2_0 := by decide +kernel
noncomputable def s2_1 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
lemma c2_1 : chunk 2 1 = s2_1 := by decide +kernel
noncomputable def s2_2 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
lemma c2_2 : chunk 2 2 = s2_2 := by decide +kernel
noncomputable def s2_3 : CBox := ⟨⟨(-17),17⟩,⟨(-17),17⟩⟩
lemma c2_3 : chunk 2 3 = s2_3 := by decide +kernel
noncomputable def s2_4 : CBox := ⟨⟨(-32),32⟩,⟨(-32),32⟩⟩
lemma c2_4 : chunk 2 4 = s2_4 := by decide +kernel
noncomputable def s2_5 : CBox := ⟨⟨(-32),32⟩,⟨(-32),32⟩⟩
lemma c2_5 : chunk 2 5 = s2_5 := by decide +kernel
noncomputable def s2_6 : CBox := ⟨⟨(-32),32⟩,⟨(-32),32⟩⟩
lemma c2_6 : chunk 2 6 = s2_6 := by decide +kernel
noncomputable def s2_7 : CBox := ⟨⟨(-32),32⟩,⟨(-32),32⟩⟩
lemma c2_7 : chunk 2 7 = s2_7 := by decide +kernel
noncomputable def s2_8 : CBox := ⟨⟨(-48),48⟩,⟨(-48),48⟩⟩
lemma c2_8 : chunk 2 8 = s2_8 := by decide +kernel
noncomputable def s2_9 : CBox := ⟨⟨(-48),48⟩,⟨(-48),48⟩⟩
lemma c2_9 : chunk 2 9 = s2_9 := by decide +kernel
noncomputable def s2_10 : CBox := ⟨⟨(-48),48⟩,⟨(-48),48⟩⟩
lemma c2_10 : chunk 2 10 = s2_10 := by decide +kernel
noncomputable def s2_11 : CBox := ⟨⟨(-48),48⟩,⟨(-48),48⟩⟩
lemma c2_11 : chunk 2 11 = s2_11 := by decide +kernel
noncomputable def s2_12 : CBox := ⟨⟨(-48),48⟩,⟨(-48),48⟩⟩
lemma c2_12 : chunk 2 12 = s2_12 := by decide +kernel
noncomputable def s2_13 : CBox := ⟨⟨(-33),33⟩,⟨(-33),33⟩⟩
lemma c2_13 : chunk 2 13 = s2_13 := by decide +kernel
noncomputable def s2_14 : CBox := ⟨⟨(-27),27⟩,⟨(-27),27⟩⟩
lemma c2_14 : chunk 2 14 = s2_14 := by decide +kernel
noncomputable def s2_15 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
lemma c2_15 : chunk 2 15 = s2_15 := by decide +kernel
noncomputable def s2 : Fin 16 → CBox := ![s2_0,s2_1,s2_2,s2_3,s2_4,s2_5,s2_6,s2_7,s2_8,s2_9,s2_10,s2_11,s2_12,s2_13,s2_14,s2_15]
lemma s2_eq (i : Fin 16) : chunk 2 i = s2 i := by
  fin_cases i
  · exact c2_0
  · exact c2_1
  · exact c2_2
  · exact c2_3
  · exact c2_4
  · exact c2_5
  · exact c2_6
  · exact c2_7
  · exact c2_8
  · exact c2_9
  · exact c2_10
  · exact c2_11
  · exact c2_12
  · exact c2_13
  · exact c2_14
  · exact c2_15
noncomputable def s3_0 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
lemma c3_0 : chunk 3 0 = s3_0 := by decide +kernel
noncomputable def s3_1 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
lemma c3_1 : chunk 3 1 = s3_1 := by decide +kernel
noncomputable def s3_2 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
lemma c3_2 : chunk 3 2 = s3_2 := by decide +kernel
noncomputable def s3_3 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
lemma c3_3 : chunk 3 3 = s3_3 := by decide +kernel
noncomputable def s3_4 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
lemma c3_4 : chunk 3 4 = s3_4 := by decide +kernel
noncomputable def s3_5 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
lemma c3_5 : chunk 3 5 = s3_5 := by decide +kernel
noncomputable def s3_6 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
lemma c3_6 : chunk 3 6 = s3_6 := by decide +kernel
noncomputable def s3_7 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
lemma c3_7 : chunk 3 7 = s3_7 := by decide +kernel
noncomputable def s3_8 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
lemma c3_8 : chunk 3 8 = s3_8 := by decide +kernel
noncomputable def s3_9 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
lemma c3_9 : chunk 3 9 = s3_9 := by decide +kernel
noncomputable def s3_10 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
lemma c3_10 : chunk 3 10 = s3_10 := by decide +kernel
noncomputable def s3_11 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
lemma c3_11 : chunk 3 11 = s3_11 := by decide +kernel
noncomputable def s3_12 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
lemma c3_12 : chunk 3 12 = s3_12 := by decide +kernel
noncomputable def s3_13 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
lemma c3_13 : chunk 3 13 = s3_13 := by decide +kernel
noncomputable def s3_14 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
lemma c3_14 : chunk 3 14 = s3_14 := by decide +kernel
noncomputable def s3_15 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
lemma c3_15 : chunk 3 15 = s3_15 := by decide +kernel
noncomputable def s3 : Fin 16 → CBox := ![s3_0,s3_1,s3_2,s3_3,s3_4,s3_5,s3_6,s3_7,s3_8,s3_9,s3_10,s3_11,s3_12,s3_13,s3_14,s3_15]
lemma s3_eq (i : Fin 16) : chunk 3 i = s3 i := by
  fin_cases i
  · exact c3_0
  · exact c3_1
  · exact c3_2
  · exact c3_3
  · exact c3_4
  · exact c3_5
  · exact c3_6
  · exact c3_7
  · exact c3_8
  · exact c3_9
  · exact c3_10
  · exact c3_11
  · exact c3_12
  · exact c3_13
  · exact c3_14
  · exact c3_15
noncomputable def s4_0 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
lemma c4_0 : chunk 4 0 = s4_0 := by decide +kernel
noncomputable def s4_1 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
lemma c4_1 : chunk 4 1 = s4_1 := by decide +kernel
noncomputable def s4_2 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
lemma c4_2 : chunk 4 2 = s4_2 := by decide +kernel
noncomputable def s4_3 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
lemma c4_3 : chunk 4 3 = s4_3 := by decide +kernel
noncomputable def s4_4 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
lemma c4_4 : chunk 4 4 = s4_4 := by decide +kernel
noncomputable def s4_5 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
lemma c4_5 : chunk 4 5 = s4_5 := by decide +kernel
noncomputable def s4_6 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
lemma c4_6 : chunk 4 6 = s4_6 := by decide +kernel
noncomputable def s4_7 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
lemma c4_7 : chunk 4 7 = s4_7 := by decide +kernel
noncomputable def s4_8 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
lemma c4_8 : chunk 4 8 = s4_8 := by decide +kernel
noncomputable def s4_9 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
lemma c4_9 : chunk 4 9 = s4_9 := by decide +kernel
noncomputable def s4_10 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
lemma c4_10 : chunk 4 10 = s4_10 := by decide +kernel
noncomputable def s4_11 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
lemma c4_11 : chunk 4 11 = s4_11 := by decide +kernel
noncomputable def s4_12 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
lemma c4_12 : chunk 4 12 = s4_12 := by decide +kernel
noncomputable def s4_13 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
lemma c4_13 : chunk 4 13 = s4_13 := by decide +kernel
noncomputable def s4_14 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
lemma c4_14 : chunk 4 14 = s4_14 := by decide +kernel
noncomputable def s4_15 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
lemma c4_15 : chunk 4 15 = s4_15 := by decide +kernel
noncomputable def s4 : Fin 16 → CBox := ![s4_0,s4_1,s4_2,s4_3,s4_4,s4_5,s4_6,s4_7,s4_8,s4_9,s4_10,s4_11,s4_12,s4_13,s4_14,s4_15]
lemma s4_eq (i : Fin 16) : chunk 4 i = s4 i := by
  fin_cases i
  · exact c4_0
  · exact c4_1
  · exact c4_2
  · exact c4_3
  · exact c4_4
  · exact c4_5
  · exact c4_6
  · exact c4_7
  · exact c4_8
  · exact c4_9
  · exact c4_10
  · exact c4_11
  · exact c4_12
  · exact c4_13
  · exact c4_14
  · exact c4_15
noncomputable def s5_0 : CBox := ⟨⟨2307776235439012604,2307890773617178532⟩,⟨(-203006940197812416658),(-203006825659634250710)⟩⟩
lemma c5_0 : chunk 5 0 = s5_0 := by decide +kernel
noncomputable def s5_1 : CBox := ⟨⟨(-186705896353946969358),(-186705676219431311502)⟩,⟨(-199656130740042112143),(-199655910605526454281)⟩⟩
lemma c5_1 : chunk 5 1 = s5_1 := by decide +kernel
noncomputable def s5_2 : CBox := ⟨⟨(-73454170721955799925),(-73454023623732597256)⟩,⟨60889060075462575191,60889207173685777858⟩⟩
lemma c5_2 : chunk 5 2 = s5_2 := by decide +kernel
noncomputable def s5_3 : CBox := ⟨⟨13602116595178667932,13602166072186426424⟩,⟨3074525814970366002,3074575291978124499⟩⟩
lemma c5_3 : chunk 5 3 = s5_3 := by decide +kernel
noncomputable def s5_4 : CBox := ⟨⟨(-881790792142502876),(-881781945011248350)⟩,⟨(-448379532422839069),(-448370685291584543)⟩⟩
lemma c5_4 : chunk 5 4 = s5_4 := by decide +kernel
noncomputable def s5_5 : CBox := ⟨⟨36148331391073578,36149151637420699⟩,⟨4337209805667606,4338030052014727⟩⟩
lemma c5_5 : chunk 5 5 = s5_5 := by decide +kernel
noncomputable def s5_6 : CBox := ⟨⟨(-540350778285447),(-540311664405033)⟩,⟨498525668893555,498564782773970⟩⟩
lemma c5_6 : chunk 5 6 = s5_6 := by decide +kernel
noncomputable def s5_7 : CBox := ⟨⟨(-3791951660474),(-3790953900443)⟩,⟨(-8089320679654),(-8088322919620)⟩⟩
lemma c5_7 : chunk 5 7 = s5_7 := by decide +kernel
noncomputable def s5_8 : CBox := ⟨⟨69404377758,69419045646⟩,⟨(-27897044840),(-27882376950)⟩⟩
lemma c5_8 : chunk 5 8 = s5_8 := by decide +kernel
noncomputable def s5_9 : CBox := ⟨⟨199671928,199812813⟩,⟨471332740,471473625⟩⟩
lemma c5_9 : chunk 5 9 = s5_9 := by decide +kernel
noncomputable def s5_10 : CBox := ⟨⟨(-3337332),(-3336232)⟩,⟨1043015,1044116⟩⟩
lemma c5_10 : chunk 5 10 = s5_10 := by decide +kernel
noncomputable def s5_11 : CBox := ⟨⟨3204,3232⟩,⟨(-29563),(-29532)⟩⟩
lemma c5_11 : chunk 5 11 = s5_11 := by decide +kernel
noncomputable def s5_12 : CBox := ⟨⟨194,215⟩,⟨330,351⟩⟩
lemma c5_12 : chunk 5 12 = s5_12 := by decide +kernel
noncomputable def s5_13 : CBox := ⟨⟨(-15),1⟩,⟨(-22),1⟩⟩
lemma c5_13 : chunk 5 13 = s5_13 := by decide +kernel
noncomputable def s5_14 : CBox := ⟨⟨(-16),15⟩,⟨(-16),16⟩⟩
lemma c5_14 : chunk 5 14 = s5_14 := by decide +kernel
noncomputable def s5_15 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
lemma c5_15 : chunk 5 15 = s5_15 := by decide +kernel
noncomputable def s5 : Fin 16 → CBox := ![s5_0,s5_1,s5_2,s5_3,s5_4,s5_5,s5_6,s5_7,s5_8,s5_9,s5_10,s5_11,s5_12,s5_13,s5_14,s5_15]
lemma s5_eq (i : Fin 16) : chunk 5 i = s5 i := by
  fin_cases i
  · exact c5_0
  · exact c5_1
  · exact c5_2
  · exact c5_3
  · exact c5_4
  · exact c5_5
  · exact c5_6
  · exact c5_7
  · exact c5_8
  · exact c5_9
  · exact c5_10
  · exact c5_11
  · exact c5_12
  · exact c5_13
  · exact c5_14
  · exact c5_15
noncomputable def sums : Fin 6 → Fin 16 → CBox := ![s0,s1,s2,s3,s4,s5]
lemma sums_eq (j : Fin 6) (i : Fin 16) : chunk j i = sums j i := by
  fin_cases j
  · exact s0_eq i
  · exact s1_eq i
  · exact s2_eq i
  · exact s3_eq i
  · exact s4_eq i
  · exact s5_eq i
noncomputable def ans : CBox := ⟨⟨(-40849393463194291847),(-40849303303956151400)⟩,⟨(-56523839493519207727),(-56523749334281067272)⟩⟩
lemma checked : cachedMomentRuleBox density0 kernel99_1 = ans := by
  change (finSum (fun j => (finSum (fun i => chunk j i)).scale 1 6)) = ans
  simp_rw [sums_eq]
  decide +kernel
lemma contains : ans.Contains (tableMomentRule false 99 1) := by
  rw [← checked]
  simpa only [Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Bool.false_eq_true,ite_false,ite_true] using @tableRule_contains_bridge false 99 true density0 kernel99_1
    density0_contains kernel99_1_contains
noncomputable def atomAnswer : CBox := ⟨⟨(-831246133391948077729),(-831246133391948055635)⟩,⟨(-183723847546026982605),(-183723847546026960516)⟩⟩
lemma atomChecked : tableAtomBox false atomKernel99_1 = atomAnswer := by decide +kernel
lemma atomContains : atomAnswer.Contains (tableMomentAtom false 99 1) := by
  rw [← atomChecked]
  exact tableAtomBox_contains false atomKernel99_1_contains
noncomputable def realAnswer : RBox := ⟨(-872095526855242369576),(-872095436695804207035)⟩
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
lemma KContains : realAnswer.Contains (tableMomentK false 99 1) := by
  rw [← realChecked]
  exact tableMomentK_contains atomContains contains (by norm_num) (by norm_num)
end tm0_99_1

namespace tm1_99_0
noncomputable def chunk (j : Fin 6) (i : Fin 16) : CBox := finSum (fun k => (density1 j i k).mul (kernel99_0 j i k))
noncomputable def s0_0 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
lemma c0_0 : chunk 0 0 = s0_0 := by decide +kernel
noncomputable def s0_1 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
lemma c0_1 : chunk 0 1 = s0_1 := by decide +kernel
noncomputable def s0_2 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
lemma c0_2 : chunk 0 2 = s0_2 := by decide +kernel
noncomputable def s0_3 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
lemma c0_3 : chunk 0 3 = s0_3 := by decide +kernel
noncomputable def s0_4 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
lemma c0_4 : chunk 0 4 = s0_4 := by decide +kernel
noncomputable def s0_5 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
lemma c0_5 : chunk 0 5 = s0_5 := by decide +kernel
noncomputable def s0_6 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
lemma c0_6 : chunk 0 6 = s0_6 := by decide +kernel
noncomputable def s0_7 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
lemma c0_7 : chunk 0 7 = s0_7 := by decide +kernel
noncomputable def s0_8 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
lemma c0_8 : chunk 0 8 = s0_8 := by decide +kernel
noncomputable def s0_9 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
lemma c0_9 : chunk 0 9 = s0_9 := by decide +kernel
noncomputable def s0_10 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
lemma c0_10 : chunk 0 10 = s0_10 := by decide +kernel
noncomputable def s0_11 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
lemma c0_11 : chunk 0 11 = s0_11 := by decide +kernel
noncomputable def s0_12 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
lemma c0_12 : chunk 0 12 = s0_12 := by decide +kernel
noncomputable def s0_13 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
lemma c0_13 : chunk 0 13 = s0_13 := by decide +kernel
noncomputable def s0_14 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
lemma c0_14 : chunk 0 14 = s0_14 := by decide +kernel
noncomputable def s0_15 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
lemma c0_15 : chunk 0 15 = s0_15 := by decide +kernel
noncomputable def s0 : Fin 16 → CBox := ![s0_0,s0_1,s0_2,s0_3,s0_4,s0_5,s0_6,s0_7,s0_8,s0_9,s0_10,s0_11,s0_12,s0_13,s0_14,s0_15]
lemma s0_eq (i : Fin 16) : chunk 0 i = s0 i := by
  fin_cases i
  · exact c0_0
  · exact c0_1
  · exact c0_2
  · exact c0_3
  · exact c0_4
  · exact c0_5
  · exact c0_6
  · exact c0_7
  · exact c0_8
  · exact c0_9
  · exact c0_10
  · exact c0_11
  · exact c0_12
  · exact c0_13
  · exact c0_14
  · exact c0_15
noncomputable def s1_0 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
lemma c1_0 : chunk 1 0 = s1_0 := by decide +kernel
noncomputable def s1_1 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
lemma c1_1 : chunk 1 1 = s1_1 := by decide +kernel
noncomputable def s1_2 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
lemma c1_2 : chunk 1 2 = s1_2 := by decide +kernel
noncomputable def s1_3 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
lemma c1_3 : chunk 1 3 = s1_3 := by decide +kernel
noncomputable def s1_4 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
lemma c1_4 : chunk 1 4 = s1_4 := by decide +kernel
noncomputable def s1_5 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
lemma c1_5 : chunk 1 5 = s1_5 := by decide +kernel
noncomputable def s1_6 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
lemma c1_6 : chunk 1 6 = s1_6 := by decide +kernel
noncomputable def s1_7 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
lemma c1_7 : chunk 1 7 = s1_7 := by decide +kernel
noncomputable def s1_8 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
lemma c1_8 : chunk 1 8 = s1_8 := by decide +kernel
noncomputable def s1_9 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
lemma c1_9 : chunk 1 9 = s1_9 := by decide +kernel
noncomputable def s1_10 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
lemma c1_10 : chunk 1 10 = s1_10 := by decide +kernel
noncomputable def s1_11 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
lemma c1_11 : chunk 1 11 = s1_11 := by decide +kernel
noncomputable def s1_12 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
lemma c1_12 : chunk 1 12 = s1_12 := by decide +kernel
noncomputable def s1_13 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
lemma c1_13 : chunk 1 13 = s1_13 := by decide +kernel
noncomputable def s1_14 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
lemma c1_14 : chunk 1 14 = s1_14 := by decide +kernel
noncomputable def s1_15 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
lemma c1_15 : chunk 1 15 = s1_15 := by decide +kernel
noncomputable def s1 : Fin 16 → CBox := ![s1_0,s1_1,s1_2,s1_3,s1_4,s1_5,s1_6,s1_7,s1_8,s1_9,s1_10,s1_11,s1_12,s1_13,s1_14,s1_15]
lemma s1_eq (i : Fin 16) : chunk 1 i = s1 i := by
  fin_cases i
  · exact c1_0
  · exact c1_1
  · exact c1_2
  · exact c1_3
  · exact c1_4
  · exact c1_5
  · exact c1_6
  · exact c1_7
  · exact c1_8
  · exact c1_9
  · exact c1_10
  · exact c1_11
  · exact c1_12
  · exact c1_13
  · exact c1_14
  · exact c1_15
noncomputable def s2_0 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
lemma c2_0 : chunk 2 0 = s2_0 := by decide +kernel
noncomputable def s2_1 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
lemma c2_1 : chunk 2 1 = s2_1 := by decide +kernel
noncomputable def s2_2 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
lemma c2_2 : chunk 2 2 = s2_2 := by decide +kernel
noncomputable def s2_3 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
lemma c2_3 : chunk 2 3 = s2_3 := by decide +kernel
noncomputable def s2_4 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
lemma c2_4 : chunk 2 4 = s2_4 := by decide +kernel
noncomputable def s2_5 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
lemma c2_5 : chunk 2 5 = s2_5 := by decide +kernel
noncomputable def s2_6 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
lemma c2_6 : chunk 2 6 = s2_6 := by decide +kernel
noncomputable def s2_7 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
lemma c2_7 : chunk 2 7 = s2_7 := by decide +kernel
noncomputable def s2_8 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
lemma c2_8 : chunk 2 8 = s2_8 := by decide +kernel
noncomputable def s2_9 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
lemma c2_9 : chunk 2 9 = s2_9 := by decide +kernel
noncomputable def s2_10 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
lemma c2_10 : chunk 2 10 = s2_10 := by decide +kernel
noncomputable def s2_11 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
lemma c2_11 : chunk 2 11 = s2_11 := by decide +kernel
noncomputable def s2_12 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
lemma c2_12 : chunk 2 12 = s2_12 := by decide +kernel
noncomputable def s2_13 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
lemma c2_13 : chunk 2 13 = s2_13 := by decide +kernel
noncomputable def s2_14 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
lemma c2_14 : chunk 2 14 = s2_14 := by decide +kernel
noncomputable def s2_15 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
lemma c2_15 : chunk 2 15 = s2_15 := by decide +kernel
noncomputable def s2 : Fin 16 → CBox := ![s2_0,s2_1,s2_2,s2_3,s2_4,s2_5,s2_6,s2_7,s2_8,s2_9,s2_10,s2_11,s2_12,s2_13,s2_14,s2_15]
lemma s2_eq (i : Fin 16) : chunk 2 i = s2 i := by
  fin_cases i
  · exact c2_0
  · exact c2_1
  · exact c2_2
  · exact c2_3
  · exact c2_4
  · exact c2_5
  · exact c2_6
  · exact c2_7
  · exact c2_8
  · exact c2_9
  · exact c2_10
  · exact c2_11
  · exact c2_12
  · exact c2_13
  · exact c2_14
  · exact c2_15
noncomputable def s3_0 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
lemma c3_0 : chunk 3 0 = s3_0 := by decide +kernel
noncomputable def s3_1 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
lemma c3_1 : chunk 3 1 = s3_1 := by decide +kernel
noncomputable def s3_2 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
lemma c3_2 : chunk 3 2 = s3_2 := by decide +kernel
noncomputable def s3_3 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
lemma c3_3 : chunk 3 3 = s3_3 := by decide +kernel
noncomputable def s3_4 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
lemma c3_4 : chunk 3 4 = s3_4 := by decide +kernel
noncomputable def s3_5 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
lemma c3_5 : chunk 3 5 = s3_5 := by decide +kernel
noncomputable def s3_6 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
lemma c3_6 : chunk 3 6 = s3_6 := by decide +kernel
noncomputable def s3_7 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
lemma c3_7 : chunk 3 7 = s3_7 := by decide +kernel
noncomputable def s3_8 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
lemma c3_8 : chunk 3 8 = s3_8 := by decide +kernel
noncomputable def s3_9 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
lemma c3_9 : chunk 3 9 = s3_9 := by decide +kernel
noncomputable def s3_10 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
lemma c3_10 : chunk 3 10 = s3_10 := by decide +kernel
noncomputable def s3_11 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
lemma c3_11 : chunk 3 11 = s3_11 := by decide +kernel
noncomputable def s3_12 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
lemma c3_12 : chunk 3 12 = s3_12 := by decide +kernel
noncomputable def s3_13 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
lemma c3_13 : chunk 3 13 = s3_13 := by decide +kernel
noncomputable def s3_14 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
lemma c3_14 : chunk 3 14 = s3_14 := by decide +kernel
noncomputable def s3_15 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
lemma c3_15 : chunk 3 15 = s3_15 := by decide +kernel
noncomputable def s3 : Fin 16 → CBox := ![s3_0,s3_1,s3_2,s3_3,s3_4,s3_5,s3_6,s3_7,s3_8,s3_9,s3_10,s3_11,s3_12,s3_13,s3_14,s3_15]
lemma s3_eq (i : Fin 16) : chunk 3 i = s3 i := by
  fin_cases i
  · exact c3_0
  · exact c3_1
  · exact c3_2
  · exact c3_3
  · exact c3_4
  · exact c3_5
  · exact c3_6
  · exact c3_7
  · exact c3_8
  · exact c3_9
  · exact c3_10
  · exact c3_11
  · exact c3_12
  · exact c3_13
  · exact c3_14
  · exact c3_15
noncomputable def s4_0 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
lemma c4_0 : chunk 4 0 = s4_0 := by decide +kernel
noncomputable def s4_1 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
lemma c4_1 : chunk 4 1 = s4_1 := by decide +kernel
noncomputable def s4_2 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
lemma c4_2 : chunk 4 2 = s4_2 := by decide +kernel
noncomputable def s4_3 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
lemma c4_3 : chunk 4 3 = s4_3 := by decide +kernel
noncomputable def s4_4 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
lemma c4_4 : chunk 4 4 = s4_4 := by decide +kernel
noncomputable def s4_5 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
lemma c4_5 : chunk 4 5 = s4_5 := by decide +kernel
noncomputable def s4_6 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
lemma c4_6 : chunk 4 6 = s4_6 := by decide +kernel
noncomputable def s4_7 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
lemma c4_7 : chunk 4 7 = s4_7 := by decide +kernel
noncomputable def s4_8 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
lemma c4_8 : chunk 4 8 = s4_8 := by decide +kernel
noncomputable def s4_9 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
lemma c4_9 : chunk 4 9 = s4_9 := by decide +kernel
noncomputable def s4_10 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
lemma c4_10 : chunk 4 10 = s4_10 := by decide +kernel
noncomputable def s4_11 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
lemma c4_11 : chunk 4 11 = s4_11 := by decide +kernel
noncomputable def s4_12 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
lemma c4_12 : chunk 4 12 = s4_12 := by decide +kernel
noncomputable def s4_13 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
lemma c4_13 : chunk 4 13 = s4_13 := by decide +kernel
noncomputable def s4_14 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
lemma c4_14 : chunk 4 14 = s4_14 := by decide +kernel
noncomputable def s4_15 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
lemma c4_15 : chunk 4 15 = s4_15 := by decide +kernel
noncomputable def s4 : Fin 16 → CBox := ![s4_0,s4_1,s4_2,s4_3,s4_4,s4_5,s4_6,s4_7,s4_8,s4_9,s4_10,s4_11,s4_12,s4_13,s4_14,s4_15]
lemma s4_eq (i : Fin 16) : chunk 4 i = s4 i := by
  fin_cases i
  · exact c4_0
  · exact c4_1
  · exact c4_2
  · exact c4_3
  · exact c4_4
  · exact c4_5
  · exact c4_6
  · exact c4_7
  · exact c4_8
  · exact c4_9
  · exact c4_10
  · exact c4_11
  · exact c4_12
  · exact c4_13
  · exact c4_14
  · exact c4_15
noncomputable def s5_0 : CBox := ⟨⟨1663334616020272547,1663335550833125771⟩,⟨32362012679542504,32362947492395725⟩⟩
lemma c5_0 : chunk 5 0 = s5_0 := by decide +kernel
noncomputable def s5_1 : CBox := ⟨⟨1310441785322591793,1310443772947861285⟩,⟨(-1693389237239220987),(-1693387249613951497)⟩⟩
lemma c5_1 : chunk 5 1 = s5_1 := by decide +kernel
noncomputable def s5_2 : CBox := ⟨⟨(-668170595700885745),(-668169169957526066)⟩,⟨(-184454844684688155),(-184453418941328476)⟩⟩
lemma c5_2 : chunk 5 2 = s5_2 := by decide +kernel
noncomputable def s5_3 : CBox := ⟨⟨137359532724230877,137360101826028711⟩,⟨63523801876760441,63524370978558275⟩⟩
lemma c5_3 : chunk 5 3 = s5_3 := by decide +kernel
noncomputable def s5_4 : CBox := ⟨⟨(-21370324135967054),(-21370106833782889)⟩,⟨(-9890676210182555),(-9890458907998390)⟩⟩
lemma c5_4 : chunk 5 4 = s5_4 := by decide +kernel
noncomputable def s5_5 : CBox := ⟨⟨1568749212517778,1568783392493959⟩,⟨264812629418949,264846809395133⟩⟩
lemma c5_5 : chunk 5 5 = s5_5 := by decide +kernel
noncomputable def s5_6 : CBox := ⟨⟨(-42812267697578),(-42809972577363)⟩,⟨24216303531427,24218598651640⟩⟩
lemma c5_6 : chunk 5 6 = s5_6 := by decide +kernel
noncomputable def s5_7 : CBox := ⟨⟨1089111509,1161684818⟩,⟨(-803157697541),(-803085124232)⟩⟩
lemma c5_7 : chunk 5 7 = s5_7 := by decide +kernel
noncomputable def s5_8 : CBox := ⟨⟨7900659026,7901867195⟩,⟨2174405798,2175613967⟩⟩
lemma c5_8 : chunk 5 8 = s5_8 := by decide +kernel
noncomputable def s5_9 : CBox := ⟨⟨(-27387117),(-27374773)⟩,⟨56980211,56992556⟩⟩
lemma c5_9 : chunk 5 9 = s5_9 := by decide +kernel
noncomputable def s5_10 : CBox := ⟨⟨(-344359),(-344246)⟩,⟨(-300082),(-299970)⟩⟩
lemma c5_10 : chunk 5 10 = s5_10 := by decide +kernel
noncomputable def s5_11 : CBox := ⟨⟨3718,3734⟩,⟨(-1215),(-1197)⟩⟩
lemma c5_11 : chunk 5 11 = s5_11 := by decide +kernel
noncomputable def s5_12 : CBox := ⟨⟨(-42),(-26)⟩,⟨32,48⟩⟩
lemma c5_12 : chunk 5 12 = s5_12 := by decide +kernel
noncomputable def s5_13 : CBox := ⟨⟨(-8),10⟩,⟨(-16),0⟩⟩
lemma c5_13 : chunk 5 13 = s5_13 := by decide +kernel
noncomputable def s5_14 : CBox := ⟨⟨(-16),11⟩,⟨(-16),15⟩⟩
lemma c5_14 : chunk 5 14 = s5_14 := by decide +kernel
noncomputable def s5_15 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
lemma c5_15 : chunk 5 15 = s5_15 := by decide +kernel
noncomputable def s5 : Fin 16 → CBox := ![s5_0,s5_1,s5_2,s5_3,s5_4,s5_5,s5_6,s5_7,s5_8,s5_9,s5_10,s5_11,s5_12,s5_13,s5_14,s5_15]
lemma s5_eq (i : Fin 16) : chunk 5 i = s5 i := by
  fin_cases i
  · exact c5_0
  · exact c5_1
  · exact c5_2
  · exact c5_3
  · exact c5_4
  · exact c5_5
  · exact c5_6
  · exact c5_7
  · exact c5_8
  · exact c5_9
  · exact c5_10
  · exact c5_11
  · exact c5_12
  · exact c5_13
  · exact c5_14
  · exact c5_15
noncomputable def sums : Fin 6 → Fin 16 → CBox := ![s0,s1,s2,s3,s4,s5]
lemma sums_eq (j : Fin 6) (i : Fin 16) : chunk j i = sums j i := by
  fin_cases j
  · exact s0_eq i
  · exact s1_eq i
  · exact s2_eq i
  · exact s3_eq i
  · exact s4_eq i
  · exact s5_eq i
noncomputable def ans : CBox := ⟨⟨403853493356184003,403854355211910240⟩,⟨(-298593452595242086),(-298592590739515849)⟩⟩
lemma checked : cachedMomentRuleBox density1 kernel99_0 = ans := by
  change (finSum (fun j => (finSum (fun i => chunk j i)).scale 1 6)) = ans
  simp_rw [sums_eq]
  decide +kernel
lemma contains : ans.Contains (tableMomentRule true 99 0) := by
  rw [← checked]
  simpa only [Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Bool.false_eq_true,ite_false,ite_true] using @tableRule_contains_bridge true 99 false density1 kernel99_0
    density1_contains kernel99_0_contains
noncomputable def atomAnswer : CBox := ⟨⟨(-81965255788817876953),(-81965255788817869353)⟩,⟨296764208284932045889,296764208284932053490⟩⟩
lemma atomChecked : tableAtomBox true atomKernel99_0 = atomAnswer := by decide +kernel
lemma atomContains : atomAnswer.Contains (tableMomentAtom true 99 0) := by
  rw [← atomChecked]
  exact tableAtomBox_contains true atomKernel99_0_contains
noncomputable def realAnswer : RBox := ⟨(-81561402295561692950),(-81561401433505959113)⟩
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
lemma KContains : realAnswer.Contains (tableMomentK true 99 0) := by
  rw [← realChecked]
  exact tableMomentK_contains atomContains contains (by norm_num) (by norm_num)
end tm1_99_0

namespace tm1_99_1
noncomputable def chunk (j : Fin 6) (i : Fin 16) : CBox := finSum (fun k => (density1 j i k).mul (kernel99_1 j i k))
noncomputable def s0_0 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
lemma c0_0 : chunk 0 0 = s0_0 := by decide +kernel
noncomputable def s0_1 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
lemma c0_1 : chunk 0 1 = s0_1 := by decide +kernel
noncomputable def s0_2 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
lemma c0_2 : chunk 0 2 = s0_2 := by decide +kernel
noncomputable def s0_3 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
lemma c0_3 : chunk 0 3 = s0_3 := by decide +kernel
noncomputable def s0_4 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
lemma c0_4 : chunk 0 4 = s0_4 := by decide +kernel
noncomputable def s0_5 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
lemma c0_5 : chunk 0 5 = s0_5 := by decide +kernel
noncomputable def s0_6 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
lemma c0_6 : chunk 0 6 = s0_6 := by decide +kernel
noncomputable def s0_7 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
lemma c0_7 : chunk 0 7 = s0_7 := by decide +kernel
noncomputable def s0_8 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
lemma c0_8 : chunk 0 8 = s0_8 := by decide +kernel
noncomputable def s0_9 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
lemma c0_9 : chunk 0 9 = s0_9 := by decide +kernel
noncomputable def s0_10 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
lemma c0_10 : chunk 0 10 = s0_10 := by decide +kernel
noncomputable def s0_11 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
lemma c0_11 : chunk 0 11 = s0_11 := by decide +kernel
noncomputable def s0_12 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
lemma c0_12 : chunk 0 12 = s0_12 := by decide +kernel
noncomputable def s0_13 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
lemma c0_13 : chunk 0 13 = s0_13 := by decide +kernel
noncomputable def s0_14 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
lemma c0_14 : chunk 0 14 = s0_14 := by decide +kernel
noncomputable def s0_15 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
lemma c0_15 : chunk 0 15 = s0_15 := by decide +kernel
noncomputable def s0 : Fin 16 → CBox := ![s0_0,s0_1,s0_2,s0_3,s0_4,s0_5,s0_6,s0_7,s0_8,s0_9,s0_10,s0_11,s0_12,s0_13,s0_14,s0_15]
lemma s0_eq (i : Fin 16) : chunk 0 i = s0 i := by
  fin_cases i
  · exact c0_0
  · exact c0_1
  · exact c0_2
  · exact c0_3
  · exact c0_4
  · exact c0_5
  · exact c0_6
  · exact c0_7
  · exact c0_8
  · exact c0_9
  · exact c0_10
  · exact c0_11
  · exact c0_12
  · exact c0_13
  · exact c0_14
  · exact c0_15
noncomputable def s1_0 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
lemma c1_0 : chunk 1 0 = s1_0 := by decide +kernel
noncomputable def s1_1 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
lemma c1_1 : chunk 1 1 = s1_1 := by decide +kernel
noncomputable def s1_2 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
lemma c1_2 : chunk 1 2 = s1_2 := by decide +kernel
noncomputable def s1_3 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
lemma c1_3 : chunk 1 3 = s1_3 := by decide +kernel
noncomputable def s1_4 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
lemma c1_4 : chunk 1 4 = s1_4 := by decide +kernel
noncomputable def s1_5 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
lemma c1_5 : chunk 1 5 = s1_5 := by decide +kernel
noncomputable def s1_6 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
lemma c1_6 : chunk 1 6 = s1_6 := by decide +kernel
noncomputable def s1_7 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
lemma c1_7 : chunk 1 7 = s1_7 := by decide +kernel
noncomputable def s1_8 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
lemma c1_8 : chunk 1 8 = s1_8 := by decide +kernel
noncomputable def s1_9 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
lemma c1_9 : chunk 1 9 = s1_9 := by decide +kernel
noncomputable def s1_10 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
lemma c1_10 : chunk 1 10 = s1_10 := by decide +kernel
noncomputable def s1_11 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
lemma c1_11 : chunk 1 11 = s1_11 := by decide +kernel
noncomputable def s1_12 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
lemma c1_12 : chunk 1 12 = s1_12 := by decide +kernel
noncomputable def s1_13 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
lemma c1_13 : chunk 1 13 = s1_13 := by decide +kernel
noncomputable def s1_14 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
lemma c1_14 : chunk 1 14 = s1_14 := by decide +kernel
noncomputable def s1_15 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
lemma c1_15 : chunk 1 15 = s1_15 := by decide +kernel
noncomputable def s1 : Fin 16 → CBox := ![s1_0,s1_1,s1_2,s1_3,s1_4,s1_5,s1_6,s1_7,s1_8,s1_9,s1_10,s1_11,s1_12,s1_13,s1_14,s1_15]
lemma s1_eq (i : Fin 16) : chunk 1 i = s1 i := by
  fin_cases i
  · exact c1_0
  · exact c1_1
  · exact c1_2
  · exact c1_3
  · exact c1_4
  · exact c1_5
  · exact c1_6
  · exact c1_7
  · exact c1_8
  · exact c1_9
  · exact c1_10
  · exact c1_11
  · exact c1_12
  · exact c1_13
  · exact c1_14
  · exact c1_15
noncomputable def s2_0 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
lemma c2_0 : chunk 2 0 = s2_0 := by decide +kernel
noncomputable def s2_1 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
lemma c2_1 : chunk 2 1 = s2_1 := by decide +kernel
noncomputable def s2_2 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
lemma c2_2 : chunk 2 2 = s2_2 := by decide +kernel
noncomputable def s2_3 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
lemma c2_3 : chunk 2 3 = s2_3 := by decide +kernel
noncomputable def s2_4 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
lemma c2_4 : chunk 2 4 = s2_4 := by decide +kernel
noncomputable def s2_5 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
lemma c2_5 : chunk 2 5 = s2_5 := by decide +kernel
noncomputable def s2_6 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
lemma c2_6 : chunk 2 6 = s2_6 := by decide +kernel
noncomputable def s2_7 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
lemma c2_7 : chunk 2 7 = s2_7 := by decide +kernel
noncomputable def s2_8 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
lemma c2_8 : chunk 2 8 = s2_8 := by decide +kernel
noncomputable def s2_9 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
lemma c2_9 : chunk 2 9 = s2_9 := by decide +kernel
noncomputable def s2_10 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
lemma c2_10 : chunk 2 10 = s2_10 := by decide +kernel
noncomputable def s2_11 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
lemma c2_11 : chunk 2 11 = s2_11 := by decide +kernel
noncomputable def s2_12 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
lemma c2_12 : chunk 2 12 = s2_12 := by decide +kernel
noncomputable def s2_13 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
lemma c2_13 : chunk 2 13 = s2_13 := by decide +kernel
noncomputable def s2_14 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
lemma c2_14 : chunk 2 14 = s2_14 := by decide +kernel
noncomputable def s2_15 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
lemma c2_15 : chunk 2 15 = s2_15 := by decide +kernel
noncomputable def s2 : Fin 16 → CBox := ![s2_0,s2_1,s2_2,s2_3,s2_4,s2_5,s2_6,s2_7,s2_8,s2_9,s2_10,s2_11,s2_12,s2_13,s2_14,s2_15]
lemma s2_eq (i : Fin 16) : chunk 2 i = s2 i := by
  fin_cases i
  · exact c2_0
  · exact c2_1
  · exact c2_2
  · exact c2_3
  · exact c2_4
  · exact c2_5
  · exact c2_6
  · exact c2_7
  · exact c2_8
  · exact c2_9
  · exact c2_10
  · exact c2_11
  · exact c2_12
  · exact c2_13
  · exact c2_14
  · exact c2_15
noncomputable def s3_0 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
lemma c3_0 : chunk 3 0 = s3_0 := by decide +kernel
noncomputable def s3_1 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
lemma c3_1 : chunk 3 1 = s3_1 := by decide +kernel
noncomputable def s3_2 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
lemma c3_2 : chunk 3 2 = s3_2 := by decide +kernel
noncomputable def s3_3 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
lemma c3_3 : chunk 3 3 = s3_3 := by decide +kernel
noncomputable def s3_4 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
lemma c3_4 : chunk 3 4 = s3_4 := by decide +kernel
noncomputable def s3_5 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
lemma c3_5 : chunk 3 5 = s3_5 := by decide +kernel
noncomputable def s3_6 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
lemma c3_6 : chunk 3 6 = s3_6 := by decide +kernel
noncomputable def s3_7 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
lemma c3_7 : chunk 3 7 = s3_7 := by decide +kernel
noncomputable def s3_8 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
lemma c3_8 : chunk 3 8 = s3_8 := by decide +kernel
noncomputable def s3_9 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
lemma c3_9 : chunk 3 9 = s3_9 := by decide +kernel
noncomputable def s3_10 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
lemma c3_10 : chunk 3 10 = s3_10 := by decide +kernel
noncomputable def s3_11 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
lemma c3_11 : chunk 3 11 = s3_11 := by decide +kernel
noncomputable def s3_12 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
lemma c3_12 : chunk 3 12 = s3_12 := by decide +kernel
noncomputable def s3_13 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
lemma c3_13 : chunk 3 13 = s3_13 := by decide +kernel
noncomputable def s3_14 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
lemma c3_14 : chunk 3 14 = s3_14 := by decide +kernel
noncomputable def s3_15 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
lemma c3_15 : chunk 3 15 = s3_15 := by decide +kernel
noncomputable def s3 : Fin 16 → CBox := ![s3_0,s3_1,s3_2,s3_3,s3_4,s3_5,s3_6,s3_7,s3_8,s3_9,s3_10,s3_11,s3_12,s3_13,s3_14,s3_15]
lemma s3_eq (i : Fin 16) : chunk 3 i = s3 i := by
  fin_cases i
  · exact c3_0
  · exact c3_1
  · exact c3_2
  · exact c3_3
  · exact c3_4
  · exact c3_5
  · exact c3_6
  · exact c3_7
  · exact c3_8
  · exact c3_9
  · exact c3_10
  · exact c3_11
  · exact c3_12
  · exact c3_13
  · exact c3_14
  · exact c3_15
noncomputable def s4_0 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
lemma c4_0 : chunk 4 0 = s4_0 := by decide +kernel
noncomputable def s4_1 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
lemma c4_1 : chunk 4 1 = s4_1 := by decide +kernel
noncomputable def s4_2 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
lemma c4_2 : chunk 4 2 = s4_2 := by decide +kernel
noncomputable def s4_3 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
lemma c4_3 : chunk 4 3 = s4_3 := by decide +kernel
noncomputable def s4_4 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
lemma c4_4 : chunk 4 4 = s4_4 := by decide +kernel
noncomputable def s4_5 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
lemma c4_5 : chunk 4 5 = s4_5 := by decide +kernel
noncomputable def s4_6 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
lemma c4_6 : chunk 4 6 = s4_6 := by decide +kernel
noncomputable def s4_7 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
lemma c4_7 : chunk 4 7 = s4_7 := by decide +kernel
noncomputable def s4_8 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
lemma c4_8 : chunk 4 8 = s4_8 := by decide +kernel
noncomputable def s4_9 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
lemma c4_9 : chunk 4 9 = s4_9 := by decide +kernel
noncomputable def s4_10 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
lemma c4_10 : chunk 4 10 = s4_10 := by decide +kernel
noncomputable def s4_11 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
lemma c4_11 : chunk 4 11 = s4_11 := by decide +kernel
noncomputable def s4_12 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
lemma c4_12 : chunk 4 12 = s4_12 := by decide +kernel
noncomputable def s4_13 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
lemma c4_13 : chunk 4 13 = s4_13 := by decide +kernel
noncomputable def s4_14 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
lemma c4_14 : chunk 4 14 = s4_14 := by decide +kernel
noncomputable def s4_15 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
lemma c4_15 : chunk 4 15 = s4_15 := by decide +kernel
noncomputable def s4 : Fin 16 → CBox := ![s4_0,s4_1,s4_2,s4_3,s4_4,s4_5,s4_6,s4_7,s4_8,s4_9,s4_10,s4_11,s4_12,s4_13,s4_14,s4_15]
lemma s4_eq (i : Fin 16) : chunk 4 i = s4 i := by
  fin_cases i
  · exact c4_0
  · exact c4_1
  · exact c4_2
  · exact c4_3
  · exact c4_4
  · exact c4_5
  · exact c4_6
  · exact c4_7
  · exact c4_8
  · exact c4_9
  · exact c4_10
  · exact c4_11
  · exact c4_12
  · exact c4_13
  · exact c4_14
  · exact c4_15
noncomputable def s5_0 : CBox := ⟨⟨(-198816464859926430),(-198812909966618582)⟩,⟨(-6015444922978207366),(-6015441368084899503)⟩⟩
lemma c5_0 : chunk 5 0 = s5_0 := by decide +kernel
noncomputable def s5_1 : CBox := ⟨⟨(-6387057718828351449),(-6387050130050216868)⟩,⟨(-4406500133094104911),(-4406492544315970326)⟩⟩
lemma c5_1 : chunk 5 1 = s5_1 := by decide +kernel
noncomputable def s5_2 : CBox := ⟨⟨(-526406732246488871),(-526401246583963044)⟩,⟨2464602438296765766,2464607923959291594⟩⟩
lemma c5_2 : chunk 5 2 = s5_2 := by decide +kernel
noncomputable def s5_3 : CBox := ⟨⟨199132321448689051,199134537670603047⟩,⟨(-516262546728425004),(-516260330506511006)⟩⟩
lemma c5_3 : chunk 5 3 = s5_3 := by decide +kernel
noncomputable def s5_4 : CBox := ⟨⟨(-30704010950084837),(-30703152362210309)⟩,⟨81165756072426933,81166614660301461⟩⟩
lemma c5_4 : chunk 5 4 = s5_4 := by decide +kernel
noncomputable def s5_5 : CBox := ⟨⟨516176913144516,516314271494942⟩,⟨(-5897787858599044),(-5897650500248621)⟩⟩
lemma c5_5 : chunk 5 5 = s5_5 := by decide +kernel
noncomputable def s5_6 : CBox := ⟨⟨105170061956259,105179465360093⟩,⟨152341222699061,152350626102900⟩⟩
lemma c5_6 : chunk 5 6 = s5_6 := by decide +kernel
noncomputable def s5_7 : CBox := ⟨⟨(-3046265604415),(-3045961923878)⟩,⟨301318297095,301621977631⟩⟩
lemma c5_7 : chunk 5 7 = s5_7 := by decide +kernel
noncomputable def s5_8 : CBox := ⟨⟨4954038335,4959206816⟩,⟨(-31264346674),(-31259178193)⟩⟩
lemma c5_8 : chunk 5 8 = s5_8 := by decide +kernel
noncomputable def s5_9 : CBox := ⟨⟨234521098,234575043⟩,⟨78989609,79043554⟩⟩
lemma c5_9 : chunk 5 9 = s5_9 := by decide +kernel
noncomputable def s5_10 : CBox := ⟨⟨(-996647),(-996196)⟩,⟨1512564,1513011⟩⟩
lemma c5_10 : chunk 5 10 = s5_10 := by decide +kernel
noncomputable def s5_11 : CBox := ⟨⟨(-6973),(-6951)⟩,⟨(-14119),(-14098)⟩⟩
lemma c5_11 : chunk 5 11 = s5_11 := by decide +kernel
noncomputable def s5_12 : CBox := ⟨⟨170,188⟩,⟨98,117⟩⟩
lemma c5_12 : chunk 5 12 = s5_12 := by decide +kernel
noncomputable def s5_13 : CBox := ⟨⟨(-16),1⟩,⟨(-10),8⟩⟩
lemma c5_13 : chunk 5 13 = s5_13 := by decide +kernel
noncomputable def s5_14 : CBox := ⟨⟨(-16),16⟩,⟨(-11),16⟩⟩
lemma c5_14 : chunk 5 14 = s5_14 := by decide +kernel
noncomputable def s5_15 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
lemma c5_15 : chunk 5 15 = s5_15 := by decide +kernel
noncomputable def s5 : Fin 16 → CBox := ![s5_0,s5_1,s5_2,s5_3,s5_4,s5_5,s5_6,s5_7,s5_8,s5_9,s5_10,s5_11,s5_12,s5_13,s5_14,s5_15]
lemma s5_eq (i : Fin 16) : chunk 5 i = s5 i := by
  fin_cases i
  · exact c5_0
  · exact c5_1
  · exact c5_2
  · exact c5_3
  · exact c5_4
  · exact c5_5
  · exact c5_6
  · exact c5_7
  · exact c5_8
  · exact c5_9
  · exact c5_10
  · exact c5_11
  · exact c5_12
  · exact c5_13
  · exact c5_14
  · exact c5_15
noncomputable def sums : Fin 6 → Fin 16 → CBox := ![s0,s1,s2,s3,s4,s5]
lemma sums_eq (j : Fin 6) (i : Fin 16) : chunk j i = sums j i := by
  fin_cases j
  · exact s0_eq i
  · exact s1_eq i
  · exact s2_eq i
  · exact s3_eq i
  · exact s4_eq i
  · exact s5_eq i
noncomputable def ans : CBox := ⟨⟨(-1157205716589851922),(-1157202408054115729)⟩,⟨(-1399697430822167887),(-1399694122286431691)⟩⟩
lemma checked : cachedMomentRuleBox density1 kernel99_1 = ans := by
  change (finSum (fun j => (finSum (fun i => chunk j i)).scale 1 6)) = ans
  simp_rw [sums_eq]
  decide +kernel
lemma contains : ans.Contains (tableMomentRule true 99 1) := by
  rw [← checked]
  simpa only [Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Bool.false_eq_true,ite_false,ite_true] using @tableRule_contains_bridge true 99 true density1 kernel99_1
    density1_contains kernel99_1_contains
noncomputable def atomAnswer : CBox := ⟨⟨1087014174435624380446,1087014174435624409338⟩,⟨240254262175573717598,240254262175573746483⟩⟩
lemma atomChecked : tableAtomBox true atomKernel99_1 = atomAnswer := by decide +kernel
lemma atomContains : atomAnswer.Contains (tableMomentAtom true 99 1) := by
  rw [← atomChecked]
  exact tableAtomBox_contains true atomKernel99_1_contains
noncomputable def realAnswer : RBox := ⟨1085856968718934528524,1085856972027670293609⟩
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
lemma KContains : realAnswer.Contains (tableMomentK true 99 1) := by
  rw [← realChecked]
  exact tableMomentK_contains atomContains contains (by norm_num) (by norm_num)
end tm1_99_1

end SharpPlanar.CachedData

end OAI
