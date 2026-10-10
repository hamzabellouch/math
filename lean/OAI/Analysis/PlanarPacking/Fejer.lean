import OAI.Analysis.PlanarPacking.Roots
import Mathlib.Tactic.FinCases

namespace OAI

/-!
# Fejér quadrature enclosures

Certified nodes and weights for the 256-node cosine quadrature rule.
-/

namespace SharpPlanar
noncomputable def fejerAngle (v : ℕ) : ℝ := Real.pi*((v:ℝ)+1/2)/256
noncomputable def fejerNode (v : ℕ) : ℝ := Real.cos (fejerAngle v)
noncomputable def fejerWeight (v : ℕ) : ℝ :=
  (1-2*∑ a ∈ Finset.Icc (1:ℕ) 127,
    Real.cos (2*(a:ℝ)*fejerAngle v)/(4*(a:ℝ)^2-1))/256


end SharpPlanar

namespace SharpPlanar
open IntegerIntervals

noncomputable def fejerPartial (v N : ℕ) : ℝ :=
  ∑ k ∈ Finset.range N,
    Real.cos (2*((k+1:ℕ):ℝ)*fejerAngle v)/(4*((k+1:ℕ):ℝ)^2-1)

lemma fejerPartial_zero (v : ℕ) : fejerPartial v 0 = 0 := by simp [fejerPartial]

lemma fejerPartial_succ (v N : ℕ) : fejerPartial v (N+1) = fejerPartial v N +
    Real.cos (2*((N+1:ℕ):ℝ)*fejerAngle v)/(4*((N+1:ℕ):ℝ)^2-1) := by
  simp only [fejerPartial,Finset.sum_range_succ]

lemma fejer_root_cos (v a : ℕ) :
    (rootPhase (2*a*(2*v+1))).re = Real.cos (2*(a:ℝ)*fejerAngle v) := by
  rw [rootPhase_cos]
  unfold fejerAngle
  congr 1
  push_cast
  ring

lemma weight_root_contains (v a n : ℕ) (b : CBox)
    (hn : (2*a*(2*v+1))%1024 = n) (hb : b.Contains (rootPhase n)) :
    b.re.Contains (Real.cos (2*(a:ℝ)*fejerAngle v)) := by
  have hh := hb.1
  rw [← hn,rootPhase_mod,fejer_root_cos] at hh
  exact hh

lemma fejerPartial_checked_step (v N n : ℕ) (a : RBox) (r : CBox) (b : RBox)
    (ha : a.Contains (fejerPartial v N))
    (hr : r.Contains (rootPhase n))
    (hn : (2*(N+1)*(2*v+1))%1024 = n)
    (he : a.add (r.re.scale 1 (4*((N+1:ℕ):ℤ)^2-1)) = b) :
    b.Contains (fejerPartial v (N+1)) := by
  rw [← he,fejerPartial_succ]
  apply RBox.contains_add ha
  have hh := RBox.contains_scale (weight_root_contains v (N+1) n r hn hr)
    1 (4*((N+1:ℕ):ℤ)^2-1) (by
      have hN : (1:ℤ) ≤ (N+1:ℕ) := by omega
      nlinarith [sq_nonneg ((N+1:ℕ):ℤ)])
  convert hh using 1
  push_cast
  ring

lemma fejer_partial_eq (v : ℕ) : fejerPartial v 127 =
    ∑ a ∈ Finset.Icc (1:ℕ) 127, Real.cos (2*(a:ℝ)*fejerAngle v)/(4*(a:ℝ)^2-1) := by
  unfold fejerPartial
  apply Finset.sum_bij (fun k _ => k+1)
  · intro k hk
    simp only [Finset.mem_Icc]
    have := Finset.mem_range.mp hk
    omega
  · intro k hk l hl hkl
    omega
  · intro k hk
    simp only [Finset.mem_Icc] at hk
    exact ⟨k-1,Finset.mem_range.mpr (by omega),by omega⟩
  · intro k hk
    rfl

lemma fejerWeight_checked (v : ℕ) (a b : RBox) (ha : a.Contains (fejerPartial v 127))
    (he : ((RBox.rat 1 1).add (a.scale (-2) 1)).scale 1 256 = b) :
    b.Contains (fejerWeight v) := by
  rw [← he]
  have hh := RBox.contains_scale (RBox.contains_add (RBox.contains_rat 1 1 (by norm_num))
    (RBox.contains_scale ha (-2) 1 (by norm_num))) 1 256 (by norm_num)
  rw [fejer_partial_eq] at hh
  convert hh using 1
  unfold fejerWeight
  push_cast
  ring

lemma fejerNode_root (v : ℕ) : fejerNode v = (rootPhase (2*v+1)).re := by
  rw [rootPhase_cos]
  unfold fejerNode fejerAngle
  congr 1
  push_cast
  ring

lemma fejerWeight_reverse (v : ℕ) (hv : v < 256) : fejerWeight (255-v) = fejerWeight v := by
  have hv' : v ≤ 255 := by omega
  have ha : fejerAngle (255-v) = Real.pi-fejerAngle v := by
    unfold fejerAngle
    rw [Nat.cast_sub hv']
    push_cast
    ring
  unfold fejerWeight
  rw [ha]
  congr 3
  apply Finset.sum_congr rfl
  intro a _
  congr 1
  rw [show 2*(a:ℝ)*(Real.pi-fejerAngle v)=(a:ℝ)*(2*Real.pi)-2*(a:ℝ)*fejerAngle v by ring]
  exact Real.cos_nat_mul_two_pi_sub _ a

end SharpPlanar

namespace SharpPlanar.IntegerCompact
open IntegerIntervals
def roots0 : Fin 32 → CBox := ![IntegerRoots.root0,IntegerRoots.root1,IntegerRoots.root2,IntegerRoots.root3,IntegerRoots.root4,IntegerRoots.root5,IntegerRoots.root6,IntegerRoots.root7,IntegerRoots.root8,IntegerRoots.root9,IntegerRoots.root10,IntegerRoots.root11,IntegerRoots.root12,IntegerRoots.root13,IntegerRoots.root14,IntegerRoots.root15,IntegerRoots.root16,IntegerRoots.root17,IntegerRoots.root18,IntegerRoots.root19,IntegerRoots.root20,IntegerRoots.root21,IntegerRoots.root22,IntegerRoots.root23,IntegerRoots.root24,IntegerRoots.root25,IntegerRoots.root26,IntegerRoots.root27,IntegerRoots.root28,IntegerRoots.root29,IntegerRoots.root30,IntegerRoots.root31]
lemma roots0_contains (j : Fin 32) : (roots0 j).Contains (rootPhase (0+j.val)) := by
  fin_cases j
  · exact IntegerRoots.root0_contains
  · exact IntegerRoots.root1_contains
  · exact IntegerRoots.root2_contains
  · exact IntegerRoots.root3_contains
  · exact IntegerRoots.root4_contains
  · exact IntegerRoots.root5_contains
  · exact IntegerRoots.root6_contains
  · exact IntegerRoots.root7_contains
  · exact IntegerRoots.root8_contains
  · exact IntegerRoots.root9_contains
  · exact IntegerRoots.root10_contains
  · exact IntegerRoots.root11_contains
  · exact IntegerRoots.root12_contains
  · exact IntegerRoots.root13_contains
  · exact IntegerRoots.root14_contains
  · exact IntegerRoots.root15_contains
  · exact IntegerRoots.root16_contains
  · exact IntegerRoots.root17_contains
  · exact IntegerRoots.root18_contains
  · exact IntegerRoots.root19_contains
  · exact IntegerRoots.root20_contains
  · exact IntegerRoots.root21_contains
  · exact IntegerRoots.root22_contains
  · exact IntegerRoots.root23_contains
  · exact IntegerRoots.root24_contains
  · exact IntegerRoots.root25_contains
  · exact IntegerRoots.root26_contains
  · exact IntegerRoots.root27_contains
  · exact IntegerRoots.root28_contains
  · exact IntegerRoots.root29_contains
  · exact IntegerRoots.root30_contains
  · exact IntegerRoots.root31_contains
def roots1 : Fin 32 → CBox := ![IntegerRoots.root32,IntegerRoots.root33,IntegerRoots.root34,IntegerRoots.root35,IntegerRoots.root36,IntegerRoots.root37,IntegerRoots.root38,IntegerRoots.root39,IntegerRoots.root40,IntegerRoots.root41,IntegerRoots.root42,IntegerRoots.root43,IntegerRoots.root44,IntegerRoots.root45,IntegerRoots.root46,IntegerRoots.root47,IntegerRoots.root48,IntegerRoots.root49,IntegerRoots.root50,IntegerRoots.root51,IntegerRoots.root52,IntegerRoots.root53,IntegerRoots.root54,IntegerRoots.root55,IntegerRoots.root56,IntegerRoots.root57,IntegerRoots.root58,IntegerRoots.root59,IntegerRoots.root60,IntegerRoots.root61,IntegerRoots.root62,IntegerRoots.root63]
lemma roots1_contains (j : Fin 32) : (roots1 j).Contains (rootPhase (32+j.val)) := by
  fin_cases j
  · exact IntegerRoots.root32_contains
  · exact IntegerRoots.root33_contains
  · exact IntegerRoots.root34_contains
  · exact IntegerRoots.root35_contains
  · exact IntegerRoots.root36_contains
  · exact IntegerRoots.root37_contains
  · exact IntegerRoots.root38_contains
  · exact IntegerRoots.root39_contains
  · exact IntegerRoots.root40_contains
  · exact IntegerRoots.root41_contains
  · exact IntegerRoots.root42_contains
  · exact IntegerRoots.root43_contains
  · exact IntegerRoots.root44_contains
  · exact IntegerRoots.root45_contains
  · exact IntegerRoots.root46_contains
  · exact IntegerRoots.root47_contains
  · exact IntegerRoots.root48_contains
  · exact IntegerRoots.root49_contains
  · exact IntegerRoots.root50_contains
  · exact IntegerRoots.root51_contains
  · exact IntegerRoots.root52_contains
  · exact IntegerRoots.root53_contains
  · exact IntegerRoots.root54_contains
  · exact IntegerRoots.root55_contains
  · exact IntegerRoots.root56_contains
  · exact IntegerRoots.root57_contains
  · exact IntegerRoots.root58_contains
  · exact IntegerRoots.root59_contains
  · exact IntegerRoots.root60_contains
  · exact IntegerRoots.root61_contains
  · exact IntegerRoots.root62_contains
  · exact IntegerRoots.root63_contains
def roots2 : Fin 32 → CBox := ![IntegerRoots.root64,IntegerRoots.root65,IntegerRoots.root66,IntegerRoots.root67,IntegerRoots.root68,IntegerRoots.root69,IntegerRoots.root70,IntegerRoots.root71,IntegerRoots.root72,IntegerRoots.root73,IntegerRoots.root74,IntegerRoots.root75,IntegerRoots.root76,IntegerRoots.root77,IntegerRoots.root78,IntegerRoots.root79,IntegerRoots.root80,IntegerRoots.root81,IntegerRoots.root82,IntegerRoots.root83,IntegerRoots.root84,IntegerRoots.root85,IntegerRoots.root86,IntegerRoots.root87,IntegerRoots.root88,IntegerRoots.root89,IntegerRoots.root90,IntegerRoots.root91,IntegerRoots.root92,IntegerRoots.root93,IntegerRoots.root94,IntegerRoots.root95]
lemma roots2_contains (j : Fin 32) : (roots2 j).Contains (rootPhase (64+j.val)) := by
  fin_cases j
  · exact IntegerRoots.root64_contains
  · exact IntegerRoots.root65_contains
  · exact IntegerRoots.root66_contains
  · exact IntegerRoots.root67_contains
  · exact IntegerRoots.root68_contains
  · exact IntegerRoots.root69_contains
  · exact IntegerRoots.root70_contains
  · exact IntegerRoots.root71_contains
  · exact IntegerRoots.root72_contains
  · exact IntegerRoots.root73_contains
  · exact IntegerRoots.root74_contains
  · exact IntegerRoots.root75_contains
  · exact IntegerRoots.root76_contains
  · exact IntegerRoots.root77_contains
  · exact IntegerRoots.root78_contains
  · exact IntegerRoots.root79_contains
  · exact IntegerRoots.root80_contains
  · exact IntegerRoots.root81_contains
  · exact IntegerRoots.root82_contains
  · exact IntegerRoots.root83_contains
  · exact IntegerRoots.root84_contains
  · exact IntegerRoots.root85_contains
  · exact IntegerRoots.root86_contains
  · exact IntegerRoots.root87_contains
  · exact IntegerRoots.root88_contains
  · exact IntegerRoots.root89_contains
  · exact IntegerRoots.root90_contains
  · exact IntegerRoots.root91_contains
  · exact IntegerRoots.root92_contains
  · exact IntegerRoots.root93_contains
  · exact IntegerRoots.root94_contains
  · exact IntegerRoots.root95_contains
def roots3 : Fin 32 → CBox := ![IntegerRoots.root96,IntegerRoots.root97,IntegerRoots.root98,IntegerRoots.root99,IntegerRoots.root100,IntegerRoots.root101,IntegerRoots.root102,IntegerRoots.root103,IntegerRoots.root104,IntegerRoots.root105,IntegerRoots.root106,IntegerRoots.root107,IntegerRoots.root108,IntegerRoots.root109,IntegerRoots.root110,IntegerRoots.root111,IntegerRoots.root112,IntegerRoots.root113,IntegerRoots.root114,IntegerRoots.root115,IntegerRoots.root116,IntegerRoots.root117,IntegerRoots.root118,IntegerRoots.root119,IntegerRoots.root120,IntegerRoots.root121,IntegerRoots.root122,IntegerRoots.root123,IntegerRoots.root124,IntegerRoots.root125,IntegerRoots.root126,IntegerRoots.root127]
lemma roots3_contains (j : Fin 32) : (roots3 j).Contains (rootPhase (96+j.val)) := by
  fin_cases j
  · exact IntegerRoots.root96_contains
  · exact IntegerRoots.root97_contains
  · exact IntegerRoots.root98_contains
  · exact IntegerRoots.root99_contains
  · exact IntegerRoots.root100_contains
  · exact IntegerRoots.root101_contains
  · exact IntegerRoots.root102_contains
  · exact IntegerRoots.root103_contains
  · exact IntegerRoots.root104_contains
  · exact IntegerRoots.root105_contains
  · exact IntegerRoots.root106_contains
  · exact IntegerRoots.root107_contains
  · exact IntegerRoots.root108_contains
  · exact IntegerRoots.root109_contains
  · exact IntegerRoots.root110_contains
  · exact IntegerRoots.root111_contains
  · exact IntegerRoots.root112_contains
  · exact IntegerRoots.root113_contains
  · exact IntegerRoots.root114_contains
  · exact IntegerRoots.root115_contains
  · exact IntegerRoots.root116_contains
  · exact IntegerRoots.root117_contains
  · exact IntegerRoots.root118_contains
  · exact IntegerRoots.root119_contains
  · exact IntegerRoots.root120_contains
  · exact IntegerRoots.root121_contains
  · exact IntegerRoots.root122_contains
  · exact IntegerRoots.root123_contains
  · exact IntegerRoots.root124_contains
  · exact IntegerRoots.root125_contains
  · exact IntegerRoots.root126_contains
  · exact IntegerRoots.root127_contains
def roots4 : Fin 32 → CBox := ![IntegerRoots.root128,IntegerRoots.root129,IntegerRoots.root130,IntegerRoots.root131,IntegerRoots.root132,IntegerRoots.root133,IntegerRoots.root134,IntegerRoots.root135,IntegerRoots.root136,IntegerRoots.root137,IntegerRoots.root138,IntegerRoots.root139,IntegerRoots.root140,IntegerRoots.root141,IntegerRoots.root142,IntegerRoots.root143,IntegerRoots.root144,IntegerRoots.root145,IntegerRoots.root146,IntegerRoots.root147,IntegerRoots.root148,IntegerRoots.root149,IntegerRoots.root150,IntegerRoots.root151,IntegerRoots.root152,IntegerRoots.root153,IntegerRoots.root154,IntegerRoots.root155,IntegerRoots.root156,IntegerRoots.root157,IntegerRoots.root158,IntegerRoots.root159]
lemma roots4_contains (j : Fin 32) : (roots4 j).Contains (rootPhase (128+j.val)) := by
  fin_cases j
  · exact IntegerRoots.root128_contains
  · exact IntegerRoots.root129_contains
  · exact IntegerRoots.root130_contains
  · exact IntegerRoots.root131_contains
  · exact IntegerRoots.root132_contains
  · exact IntegerRoots.root133_contains
  · exact IntegerRoots.root134_contains
  · exact IntegerRoots.root135_contains
  · exact IntegerRoots.root136_contains
  · exact IntegerRoots.root137_contains
  · exact IntegerRoots.root138_contains
  · exact IntegerRoots.root139_contains
  · exact IntegerRoots.root140_contains
  · exact IntegerRoots.root141_contains
  · exact IntegerRoots.root142_contains
  · exact IntegerRoots.root143_contains
  · exact IntegerRoots.root144_contains
  · exact IntegerRoots.root145_contains
  · exact IntegerRoots.root146_contains
  · exact IntegerRoots.root147_contains
  · exact IntegerRoots.root148_contains
  · exact IntegerRoots.root149_contains
  · exact IntegerRoots.root150_contains
  · exact IntegerRoots.root151_contains
  · exact IntegerRoots.root152_contains
  · exact IntegerRoots.root153_contains
  · exact IntegerRoots.root154_contains
  · exact IntegerRoots.root155_contains
  · exact IntegerRoots.root156_contains
  · exact IntegerRoots.root157_contains
  · exact IntegerRoots.root158_contains
  · exact IntegerRoots.root159_contains
def roots5 : Fin 32 → CBox := ![IntegerRoots.root160,IntegerRoots.root161,IntegerRoots.root162,IntegerRoots.root163,IntegerRoots.root164,IntegerRoots.root165,IntegerRoots.root166,IntegerRoots.root167,IntegerRoots.root168,IntegerRoots.root169,IntegerRoots.root170,IntegerRoots.root171,IntegerRoots.root172,IntegerRoots.root173,IntegerRoots.root174,IntegerRoots.root175,IntegerRoots.root176,IntegerRoots.root177,IntegerRoots.root178,IntegerRoots.root179,IntegerRoots.root180,IntegerRoots.root181,IntegerRoots.root182,IntegerRoots.root183,IntegerRoots.root184,IntegerRoots.root185,IntegerRoots.root186,IntegerRoots.root187,IntegerRoots.root188,IntegerRoots.root189,IntegerRoots.root190,IntegerRoots.root191]
lemma roots5_contains (j : Fin 32) : (roots5 j).Contains (rootPhase (160+j.val)) := by
  fin_cases j
  · exact IntegerRoots.root160_contains
  · exact IntegerRoots.root161_contains
  · exact IntegerRoots.root162_contains
  · exact IntegerRoots.root163_contains
  · exact IntegerRoots.root164_contains
  · exact IntegerRoots.root165_contains
  · exact IntegerRoots.root166_contains
  · exact IntegerRoots.root167_contains
  · exact IntegerRoots.root168_contains
  · exact IntegerRoots.root169_contains
  · exact IntegerRoots.root170_contains
  · exact IntegerRoots.root171_contains
  · exact IntegerRoots.root172_contains
  · exact IntegerRoots.root173_contains
  · exact IntegerRoots.root174_contains
  · exact IntegerRoots.root175_contains
  · exact IntegerRoots.root176_contains
  · exact IntegerRoots.root177_contains
  · exact IntegerRoots.root178_contains
  · exact IntegerRoots.root179_contains
  · exact IntegerRoots.root180_contains
  · exact IntegerRoots.root181_contains
  · exact IntegerRoots.root182_contains
  · exact IntegerRoots.root183_contains
  · exact IntegerRoots.root184_contains
  · exact IntegerRoots.root185_contains
  · exact IntegerRoots.root186_contains
  · exact IntegerRoots.root187_contains
  · exact IntegerRoots.root188_contains
  · exact IntegerRoots.root189_contains
  · exact IntegerRoots.root190_contains
  · exact IntegerRoots.root191_contains
def roots6 : Fin 32 → CBox := ![IntegerRoots.root192,IntegerRoots.root193,IntegerRoots.root194,IntegerRoots.root195,IntegerRoots.root196,IntegerRoots.root197,IntegerRoots.root198,IntegerRoots.root199,IntegerRoots.root200,IntegerRoots.root201,IntegerRoots.root202,IntegerRoots.root203,IntegerRoots.root204,IntegerRoots.root205,IntegerRoots.root206,IntegerRoots.root207,IntegerRoots.root208,IntegerRoots.root209,IntegerRoots.root210,IntegerRoots.root211,IntegerRoots.root212,IntegerRoots.root213,IntegerRoots.root214,IntegerRoots.root215,IntegerRoots.root216,IntegerRoots.root217,IntegerRoots.root218,IntegerRoots.root219,IntegerRoots.root220,IntegerRoots.root221,IntegerRoots.root222,IntegerRoots.root223]
lemma roots6_contains (j : Fin 32) : (roots6 j).Contains (rootPhase (192+j.val)) := by
  fin_cases j
  · exact IntegerRoots.root192_contains
  · exact IntegerRoots.root193_contains
  · exact IntegerRoots.root194_contains
  · exact IntegerRoots.root195_contains
  · exact IntegerRoots.root196_contains
  · exact IntegerRoots.root197_contains
  · exact IntegerRoots.root198_contains
  · exact IntegerRoots.root199_contains
  · exact IntegerRoots.root200_contains
  · exact IntegerRoots.root201_contains
  · exact IntegerRoots.root202_contains
  · exact IntegerRoots.root203_contains
  · exact IntegerRoots.root204_contains
  · exact IntegerRoots.root205_contains
  · exact IntegerRoots.root206_contains
  · exact IntegerRoots.root207_contains
  · exact IntegerRoots.root208_contains
  · exact IntegerRoots.root209_contains
  · exact IntegerRoots.root210_contains
  · exact IntegerRoots.root211_contains
  · exact IntegerRoots.root212_contains
  · exact IntegerRoots.root213_contains
  · exact IntegerRoots.root214_contains
  · exact IntegerRoots.root215_contains
  · exact IntegerRoots.root216_contains
  · exact IntegerRoots.root217_contains
  · exact IntegerRoots.root218_contains
  · exact IntegerRoots.root219_contains
  · exact IntegerRoots.root220_contains
  · exact IntegerRoots.root221_contains
  · exact IntegerRoots.root222_contains
  · exact IntegerRoots.root223_contains
def roots7 : Fin 32 → CBox := ![IntegerRoots.root224,IntegerRoots.root225,IntegerRoots.root226,IntegerRoots.root227,IntegerRoots.root228,IntegerRoots.root229,IntegerRoots.root230,IntegerRoots.root231,IntegerRoots.root232,IntegerRoots.root233,IntegerRoots.root234,IntegerRoots.root235,IntegerRoots.root236,IntegerRoots.root237,IntegerRoots.root238,IntegerRoots.root239,IntegerRoots.root240,IntegerRoots.root241,IntegerRoots.root242,IntegerRoots.root243,IntegerRoots.root244,IntegerRoots.root245,IntegerRoots.root246,IntegerRoots.root247,IntegerRoots.root248,IntegerRoots.root249,IntegerRoots.root250,IntegerRoots.root251,IntegerRoots.root252,IntegerRoots.root253,IntegerRoots.root254,IntegerRoots.root255]
lemma roots7_contains (j : Fin 32) : (roots7 j).Contains (rootPhase (224+j.val)) := by
  fin_cases j
  · exact IntegerRoots.root224_contains
  · exact IntegerRoots.root225_contains
  · exact IntegerRoots.root226_contains
  · exact IntegerRoots.root227_contains
  · exact IntegerRoots.root228_contains
  · exact IntegerRoots.root229_contains
  · exact IntegerRoots.root230_contains
  · exact IntegerRoots.root231_contains
  · exact IntegerRoots.root232_contains
  · exact IntegerRoots.root233_contains
  · exact IntegerRoots.root234_contains
  · exact IntegerRoots.root235_contains
  · exact IntegerRoots.root236_contains
  · exact IntegerRoots.root237_contains
  · exact IntegerRoots.root238_contains
  · exact IntegerRoots.root239_contains
  · exact IntegerRoots.root240_contains
  · exact IntegerRoots.root241_contains
  · exact IntegerRoots.root242_contains
  · exact IntegerRoots.root243_contains
  · exact IntegerRoots.root244_contains
  · exact IntegerRoots.root245_contains
  · exact IntegerRoots.root246_contains
  · exact IntegerRoots.root247_contains
  · exact IntegerRoots.root248_contains
  · exact IntegerRoots.root249_contains
  · exact IntegerRoots.root250_contains
  · exact IntegerRoots.root251_contains
  · exact IntegerRoots.root252_contains
  · exact IntegerRoots.root253_contains
  · exact IntegerRoots.root254_contains
  · exact IntegerRoots.root255_contains
def roots8 : Fin 32 → CBox := ![IntegerRoots.root256,IntegerRoots.root257,IntegerRoots.root258,IntegerRoots.root259,IntegerRoots.root260,IntegerRoots.root261,IntegerRoots.root262,IntegerRoots.root263,IntegerRoots.root264,IntegerRoots.root265,IntegerRoots.root266,IntegerRoots.root267,IntegerRoots.root268,IntegerRoots.root269,IntegerRoots.root270,IntegerRoots.root271,IntegerRoots.root272,IntegerRoots.root273,IntegerRoots.root274,IntegerRoots.root275,IntegerRoots.root276,IntegerRoots.root277,IntegerRoots.root278,IntegerRoots.root279,IntegerRoots.root280,IntegerRoots.root281,IntegerRoots.root282,IntegerRoots.root283,IntegerRoots.root284,IntegerRoots.root285,IntegerRoots.root286,IntegerRoots.root287]
lemma roots8_contains (j : Fin 32) : (roots8 j).Contains (rootPhase (256+j.val)) := by
  fin_cases j
  · exact IntegerRoots.root256_contains
  · exact IntegerRoots.root257_contains
  · exact IntegerRoots.root258_contains
  · exact IntegerRoots.root259_contains
  · exact IntegerRoots.root260_contains
  · exact IntegerRoots.root261_contains
  · exact IntegerRoots.root262_contains
  · exact IntegerRoots.root263_contains
  · exact IntegerRoots.root264_contains
  · exact IntegerRoots.root265_contains
  · exact IntegerRoots.root266_contains
  · exact IntegerRoots.root267_contains
  · exact IntegerRoots.root268_contains
  · exact IntegerRoots.root269_contains
  · exact IntegerRoots.root270_contains
  · exact IntegerRoots.root271_contains
  · exact IntegerRoots.root272_contains
  · exact IntegerRoots.root273_contains
  · exact IntegerRoots.root274_contains
  · exact IntegerRoots.root275_contains
  · exact IntegerRoots.root276_contains
  · exact IntegerRoots.root277_contains
  · exact IntegerRoots.root278_contains
  · exact IntegerRoots.root279_contains
  · exact IntegerRoots.root280_contains
  · exact IntegerRoots.root281_contains
  · exact IntegerRoots.root282_contains
  · exact IntegerRoots.root283_contains
  · exact IntegerRoots.root284_contains
  · exact IntegerRoots.root285_contains
  · exact IntegerRoots.root286_contains
  · exact IntegerRoots.root287_contains
def roots9 : Fin 32 → CBox := ![IntegerRoots.root288,IntegerRoots.root289,IntegerRoots.root290,IntegerRoots.root291,IntegerRoots.root292,IntegerRoots.root293,IntegerRoots.root294,IntegerRoots.root295,IntegerRoots.root296,IntegerRoots.root297,IntegerRoots.root298,IntegerRoots.root299,IntegerRoots.root300,IntegerRoots.root301,IntegerRoots.root302,IntegerRoots.root303,IntegerRoots.root304,IntegerRoots.root305,IntegerRoots.root306,IntegerRoots.root307,IntegerRoots.root308,IntegerRoots.root309,IntegerRoots.root310,IntegerRoots.root311,IntegerRoots.root312,IntegerRoots.root313,IntegerRoots.root314,IntegerRoots.root315,IntegerRoots.root316,IntegerRoots.root317,IntegerRoots.root318,IntegerRoots.root319]
lemma roots9_contains (j : Fin 32) : (roots9 j).Contains (rootPhase (288+j.val)) := by
  fin_cases j
  · exact IntegerRoots.root288_contains
  · exact IntegerRoots.root289_contains
  · exact IntegerRoots.root290_contains
  · exact IntegerRoots.root291_contains
  · exact IntegerRoots.root292_contains
  · exact IntegerRoots.root293_contains
  · exact IntegerRoots.root294_contains
  · exact IntegerRoots.root295_contains
  · exact IntegerRoots.root296_contains
  · exact IntegerRoots.root297_contains
  · exact IntegerRoots.root298_contains
  · exact IntegerRoots.root299_contains
  · exact IntegerRoots.root300_contains
  · exact IntegerRoots.root301_contains
  · exact IntegerRoots.root302_contains
  · exact IntegerRoots.root303_contains
  · exact IntegerRoots.root304_contains
  · exact IntegerRoots.root305_contains
  · exact IntegerRoots.root306_contains
  · exact IntegerRoots.root307_contains
  · exact IntegerRoots.root308_contains
  · exact IntegerRoots.root309_contains
  · exact IntegerRoots.root310_contains
  · exact IntegerRoots.root311_contains
  · exact IntegerRoots.root312_contains
  · exact IntegerRoots.root313_contains
  · exact IntegerRoots.root314_contains
  · exact IntegerRoots.root315_contains
  · exact IntegerRoots.root316_contains
  · exact IntegerRoots.root317_contains
  · exact IntegerRoots.root318_contains
  · exact IntegerRoots.root319_contains
def roots10 : Fin 32 → CBox := ![IntegerRoots.root320,IntegerRoots.root321,IntegerRoots.root322,IntegerRoots.root323,IntegerRoots.root324,IntegerRoots.root325,IntegerRoots.root326,IntegerRoots.root327,IntegerRoots.root328,IntegerRoots.root329,IntegerRoots.root330,IntegerRoots.root331,IntegerRoots.root332,IntegerRoots.root333,IntegerRoots.root334,IntegerRoots.root335,IntegerRoots.root336,IntegerRoots.root337,IntegerRoots.root338,IntegerRoots.root339,IntegerRoots.root340,IntegerRoots.root341,IntegerRoots.root342,IntegerRoots.root343,IntegerRoots.root344,IntegerRoots.root345,IntegerRoots.root346,IntegerRoots.root347,IntegerRoots.root348,IntegerRoots.root349,IntegerRoots.root350,IntegerRoots.root351]
lemma roots10_contains (j : Fin 32) : (roots10 j).Contains (rootPhase (320+j.val)) := by
  fin_cases j
  · exact IntegerRoots.root320_contains
  · exact IntegerRoots.root321_contains
  · exact IntegerRoots.root322_contains
  · exact IntegerRoots.root323_contains
  · exact IntegerRoots.root324_contains
  · exact IntegerRoots.root325_contains
  · exact IntegerRoots.root326_contains
  · exact IntegerRoots.root327_contains
  · exact IntegerRoots.root328_contains
  · exact IntegerRoots.root329_contains
  · exact IntegerRoots.root330_contains
  · exact IntegerRoots.root331_contains
  · exact IntegerRoots.root332_contains
  · exact IntegerRoots.root333_contains
  · exact IntegerRoots.root334_contains
  · exact IntegerRoots.root335_contains
  · exact IntegerRoots.root336_contains
  · exact IntegerRoots.root337_contains
  · exact IntegerRoots.root338_contains
  · exact IntegerRoots.root339_contains
  · exact IntegerRoots.root340_contains
  · exact IntegerRoots.root341_contains
  · exact IntegerRoots.root342_contains
  · exact IntegerRoots.root343_contains
  · exact IntegerRoots.root344_contains
  · exact IntegerRoots.root345_contains
  · exact IntegerRoots.root346_contains
  · exact IntegerRoots.root347_contains
  · exact IntegerRoots.root348_contains
  · exact IntegerRoots.root349_contains
  · exact IntegerRoots.root350_contains
  · exact IntegerRoots.root351_contains
def roots11 : Fin 32 → CBox := ![IntegerRoots.root352,IntegerRoots.root353,IntegerRoots.root354,IntegerRoots.root355,IntegerRoots.root356,IntegerRoots.root357,IntegerRoots.root358,IntegerRoots.root359,IntegerRoots.root360,IntegerRoots.root361,IntegerRoots.root362,IntegerRoots.root363,IntegerRoots.root364,IntegerRoots.root365,IntegerRoots.root366,IntegerRoots.root367,IntegerRoots.root368,IntegerRoots.root369,IntegerRoots.root370,IntegerRoots.root371,IntegerRoots.root372,IntegerRoots.root373,IntegerRoots.root374,IntegerRoots.root375,IntegerRoots.root376,IntegerRoots.root377,IntegerRoots.root378,IntegerRoots.root379,IntegerRoots.root380,IntegerRoots.root381,IntegerRoots.root382,IntegerRoots.root383]
lemma roots11_contains (j : Fin 32) : (roots11 j).Contains (rootPhase (352+j.val)) := by
  fin_cases j
  · exact IntegerRoots.root352_contains
  · exact IntegerRoots.root353_contains
  · exact IntegerRoots.root354_contains
  · exact IntegerRoots.root355_contains
  · exact IntegerRoots.root356_contains
  · exact IntegerRoots.root357_contains
  · exact IntegerRoots.root358_contains
  · exact IntegerRoots.root359_contains
  · exact IntegerRoots.root360_contains
  · exact IntegerRoots.root361_contains
  · exact IntegerRoots.root362_contains
  · exact IntegerRoots.root363_contains
  · exact IntegerRoots.root364_contains
  · exact IntegerRoots.root365_contains
  · exact IntegerRoots.root366_contains
  · exact IntegerRoots.root367_contains
  · exact IntegerRoots.root368_contains
  · exact IntegerRoots.root369_contains
  · exact IntegerRoots.root370_contains
  · exact IntegerRoots.root371_contains
  · exact IntegerRoots.root372_contains
  · exact IntegerRoots.root373_contains
  · exact IntegerRoots.root374_contains
  · exact IntegerRoots.root375_contains
  · exact IntegerRoots.root376_contains
  · exact IntegerRoots.root377_contains
  · exact IntegerRoots.root378_contains
  · exact IntegerRoots.root379_contains
  · exact IntegerRoots.root380_contains
  · exact IntegerRoots.root381_contains
  · exact IntegerRoots.root382_contains
  · exact IntegerRoots.root383_contains
def roots12 : Fin 32 → CBox := ![IntegerRoots.root384,IntegerRoots.root385,IntegerRoots.root386,IntegerRoots.root387,IntegerRoots.root388,IntegerRoots.root389,IntegerRoots.root390,IntegerRoots.root391,IntegerRoots.root392,IntegerRoots.root393,IntegerRoots.root394,IntegerRoots.root395,IntegerRoots.root396,IntegerRoots.root397,IntegerRoots.root398,IntegerRoots.root399,IntegerRoots.root400,IntegerRoots.root401,IntegerRoots.root402,IntegerRoots.root403,IntegerRoots.root404,IntegerRoots.root405,IntegerRoots.root406,IntegerRoots.root407,IntegerRoots.root408,IntegerRoots.root409,IntegerRoots.root410,IntegerRoots.root411,IntegerRoots.root412,IntegerRoots.root413,IntegerRoots.root414,IntegerRoots.root415]
lemma roots12_contains (j : Fin 32) : (roots12 j).Contains (rootPhase (384+j.val)) := by
  fin_cases j
  · exact IntegerRoots.root384_contains
  · exact IntegerRoots.root385_contains
  · exact IntegerRoots.root386_contains
  · exact IntegerRoots.root387_contains
  · exact IntegerRoots.root388_contains
  · exact IntegerRoots.root389_contains
  · exact IntegerRoots.root390_contains
  · exact IntegerRoots.root391_contains
  · exact IntegerRoots.root392_contains
  · exact IntegerRoots.root393_contains
  · exact IntegerRoots.root394_contains
  · exact IntegerRoots.root395_contains
  · exact IntegerRoots.root396_contains
  · exact IntegerRoots.root397_contains
  · exact IntegerRoots.root398_contains
  · exact IntegerRoots.root399_contains
  · exact IntegerRoots.root400_contains
  · exact IntegerRoots.root401_contains
  · exact IntegerRoots.root402_contains
  · exact IntegerRoots.root403_contains
  · exact IntegerRoots.root404_contains
  · exact IntegerRoots.root405_contains
  · exact IntegerRoots.root406_contains
  · exact IntegerRoots.root407_contains
  · exact IntegerRoots.root408_contains
  · exact IntegerRoots.root409_contains
  · exact IntegerRoots.root410_contains
  · exact IntegerRoots.root411_contains
  · exact IntegerRoots.root412_contains
  · exact IntegerRoots.root413_contains
  · exact IntegerRoots.root414_contains
  · exact IntegerRoots.root415_contains
def roots13 : Fin 32 → CBox := ![IntegerRoots.root416,IntegerRoots.root417,IntegerRoots.root418,IntegerRoots.root419,IntegerRoots.root420,IntegerRoots.root421,IntegerRoots.root422,IntegerRoots.root423,IntegerRoots.root424,IntegerRoots.root425,IntegerRoots.root426,IntegerRoots.root427,IntegerRoots.root428,IntegerRoots.root429,IntegerRoots.root430,IntegerRoots.root431,IntegerRoots.root432,IntegerRoots.root433,IntegerRoots.root434,IntegerRoots.root435,IntegerRoots.root436,IntegerRoots.root437,IntegerRoots.root438,IntegerRoots.root439,IntegerRoots.root440,IntegerRoots.root441,IntegerRoots.root442,IntegerRoots.root443,IntegerRoots.root444,IntegerRoots.root445,IntegerRoots.root446,IntegerRoots.root447]
lemma roots13_contains (j : Fin 32) : (roots13 j).Contains (rootPhase (416+j.val)) := by
  fin_cases j
  · exact IntegerRoots.root416_contains
  · exact IntegerRoots.root417_contains
  · exact IntegerRoots.root418_contains
  · exact IntegerRoots.root419_contains
  · exact IntegerRoots.root420_contains
  · exact IntegerRoots.root421_contains
  · exact IntegerRoots.root422_contains
  · exact IntegerRoots.root423_contains
  · exact IntegerRoots.root424_contains
  · exact IntegerRoots.root425_contains
  · exact IntegerRoots.root426_contains
  · exact IntegerRoots.root427_contains
  · exact IntegerRoots.root428_contains
  · exact IntegerRoots.root429_contains
  · exact IntegerRoots.root430_contains
  · exact IntegerRoots.root431_contains
  · exact IntegerRoots.root432_contains
  · exact IntegerRoots.root433_contains
  · exact IntegerRoots.root434_contains
  · exact IntegerRoots.root435_contains
  · exact IntegerRoots.root436_contains
  · exact IntegerRoots.root437_contains
  · exact IntegerRoots.root438_contains
  · exact IntegerRoots.root439_contains
  · exact IntegerRoots.root440_contains
  · exact IntegerRoots.root441_contains
  · exact IntegerRoots.root442_contains
  · exact IntegerRoots.root443_contains
  · exact IntegerRoots.root444_contains
  · exact IntegerRoots.root445_contains
  · exact IntegerRoots.root446_contains
  · exact IntegerRoots.root447_contains
def roots14 : Fin 32 → CBox := ![IntegerRoots.root448,IntegerRoots.root449,IntegerRoots.root450,IntegerRoots.root451,IntegerRoots.root452,IntegerRoots.root453,IntegerRoots.root454,IntegerRoots.root455,IntegerRoots.root456,IntegerRoots.root457,IntegerRoots.root458,IntegerRoots.root459,IntegerRoots.root460,IntegerRoots.root461,IntegerRoots.root462,IntegerRoots.root463,IntegerRoots.root464,IntegerRoots.root465,IntegerRoots.root466,IntegerRoots.root467,IntegerRoots.root468,IntegerRoots.root469,IntegerRoots.root470,IntegerRoots.root471,IntegerRoots.root472,IntegerRoots.root473,IntegerRoots.root474,IntegerRoots.root475,IntegerRoots.root476,IntegerRoots.root477,IntegerRoots.root478,IntegerRoots.root479]
lemma roots14_contains (j : Fin 32) : (roots14 j).Contains (rootPhase (448+j.val)) := by
  fin_cases j
  · exact IntegerRoots.root448_contains
  · exact IntegerRoots.root449_contains
  · exact IntegerRoots.root450_contains
  · exact IntegerRoots.root451_contains
  · exact IntegerRoots.root452_contains
  · exact IntegerRoots.root453_contains
  · exact IntegerRoots.root454_contains
  · exact IntegerRoots.root455_contains
  · exact IntegerRoots.root456_contains
  · exact IntegerRoots.root457_contains
  · exact IntegerRoots.root458_contains
  · exact IntegerRoots.root459_contains
  · exact IntegerRoots.root460_contains
  · exact IntegerRoots.root461_contains
  · exact IntegerRoots.root462_contains
  · exact IntegerRoots.root463_contains
  · exact IntegerRoots.root464_contains
  · exact IntegerRoots.root465_contains
  · exact IntegerRoots.root466_contains
  · exact IntegerRoots.root467_contains
  · exact IntegerRoots.root468_contains
  · exact IntegerRoots.root469_contains
  · exact IntegerRoots.root470_contains
  · exact IntegerRoots.root471_contains
  · exact IntegerRoots.root472_contains
  · exact IntegerRoots.root473_contains
  · exact IntegerRoots.root474_contains
  · exact IntegerRoots.root475_contains
  · exact IntegerRoots.root476_contains
  · exact IntegerRoots.root477_contains
  · exact IntegerRoots.root478_contains
  · exact IntegerRoots.root479_contains
def roots15 : Fin 32 → CBox := ![IntegerRoots.root480,IntegerRoots.root481,IntegerRoots.root482,IntegerRoots.root483,IntegerRoots.root484,IntegerRoots.root485,IntegerRoots.root486,IntegerRoots.root487,IntegerRoots.root488,IntegerRoots.root489,IntegerRoots.root490,IntegerRoots.root491,IntegerRoots.root492,IntegerRoots.root493,IntegerRoots.root494,IntegerRoots.root495,IntegerRoots.root496,IntegerRoots.root497,IntegerRoots.root498,IntegerRoots.root499,IntegerRoots.root500,IntegerRoots.root501,IntegerRoots.root502,IntegerRoots.root503,IntegerRoots.root504,IntegerRoots.root505,IntegerRoots.root506,IntegerRoots.root507,IntegerRoots.root508,IntegerRoots.root509,IntegerRoots.root510,IntegerRoots.root511]
lemma roots15_contains (j : Fin 32) : (roots15 j).Contains (rootPhase (480+j.val)) := by
  fin_cases j
  · exact IntegerRoots.root480_contains
  · exact IntegerRoots.root481_contains
  · exact IntegerRoots.root482_contains
  · exact IntegerRoots.root483_contains
  · exact IntegerRoots.root484_contains
  · exact IntegerRoots.root485_contains
  · exact IntegerRoots.root486_contains
  · exact IntegerRoots.root487_contains
  · exact IntegerRoots.root488_contains
  · exact IntegerRoots.root489_contains
  · exact IntegerRoots.root490_contains
  · exact IntegerRoots.root491_contains
  · exact IntegerRoots.root492_contains
  · exact IntegerRoots.root493_contains
  · exact IntegerRoots.root494_contains
  · exact IntegerRoots.root495_contains
  · exact IntegerRoots.root496_contains
  · exact IntegerRoots.root497_contains
  · exact IntegerRoots.root498_contains
  · exact IntegerRoots.root499_contains
  · exact IntegerRoots.root500_contains
  · exact IntegerRoots.root501_contains
  · exact IntegerRoots.root502_contains
  · exact IntegerRoots.root503_contains
  · exact IntegerRoots.root504_contains
  · exact IntegerRoots.root505_contains
  · exact IntegerRoots.root506_contains
  · exact IntegerRoots.root507_contains
  · exact IntegerRoots.root508_contains
  · exact IntegerRoots.root509_contains
  · exact IntegerRoots.root510_contains
  · exact IntegerRoots.root511_contains
def roots16 : Fin 32 → CBox := ![IntegerRoots.root512,IntegerRoots.root513,IntegerRoots.root514,IntegerRoots.root515,IntegerRoots.root516,IntegerRoots.root517,IntegerRoots.root518,IntegerRoots.root519,IntegerRoots.root520,IntegerRoots.root521,IntegerRoots.root522,IntegerRoots.root523,IntegerRoots.root524,IntegerRoots.root525,IntegerRoots.root526,IntegerRoots.root527,IntegerRoots.root528,IntegerRoots.root529,IntegerRoots.root530,IntegerRoots.root531,IntegerRoots.root532,IntegerRoots.root533,IntegerRoots.root534,IntegerRoots.root535,IntegerRoots.root536,IntegerRoots.root537,IntegerRoots.root538,IntegerRoots.root539,IntegerRoots.root540,IntegerRoots.root541,IntegerRoots.root542,IntegerRoots.root543]
lemma roots16_contains (j : Fin 32) : (roots16 j).Contains (rootPhase (512+j.val)) := by
  fin_cases j
  · exact IntegerRoots.root512_contains
  · exact IntegerRoots.root513_contains
  · exact IntegerRoots.root514_contains
  · exact IntegerRoots.root515_contains
  · exact IntegerRoots.root516_contains
  · exact IntegerRoots.root517_contains
  · exact IntegerRoots.root518_contains
  · exact IntegerRoots.root519_contains
  · exact IntegerRoots.root520_contains
  · exact IntegerRoots.root521_contains
  · exact IntegerRoots.root522_contains
  · exact IntegerRoots.root523_contains
  · exact IntegerRoots.root524_contains
  · exact IntegerRoots.root525_contains
  · exact IntegerRoots.root526_contains
  · exact IntegerRoots.root527_contains
  · exact IntegerRoots.root528_contains
  · exact IntegerRoots.root529_contains
  · exact IntegerRoots.root530_contains
  · exact IntegerRoots.root531_contains
  · exact IntegerRoots.root532_contains
  · exact IntegerRoots.root533_contains
  · exact IntegerRoots.root534_contains
  · exact IntegerRoots.root535_contains
  · exact IntegerRoots.root536_contains
  · exact IntegerRoots.root537_contains
  · exact IntegerRoots.root538_contains
  · exact IntegerRoots.root539_contains
  · exact IntegerRoots.root540_contains
  · exact IntegerRoots.root541_contains
  · exact IntegerRoots.root542_contains
  · exact IntegerRoots.root543_contains
def roots17 : Fin 32 → CBox := ![IntegerRoots.root544,IntegerRoots.root545,IntegerRoots.root546,IntegerRoots.root547,IntegerRoots.root548,IntegerRoots.root549,IntegerRoots.root550,IntegerRoots.root551,IntegerRoots.root552,IntegerRoots.root553,IntegerRoots.root554,IntegerRoots.root555,IntegerRoots.root556,IntegerRoots.root557,IntegerRoots.root558,IntegerRoots.root559,IntegerRoots.root560,IntegerRoots.root561,IntegerRoots.root562,IntegerRoots.root563,IntegerRoots.root564,IntegerRoots.root565,IntegerRoots.root566,IntegerRoots.root567,IntegerRoots.root568,IntegerRoots.root569,IntegerRoots.root570,IntegerRoots.root571,IntegerRoots.root572,IntegerRoots.root573,IntegerRoots.root574,IntegerRoots.root575]
lemma roots17_contains (j : Fin 32) : (roots17 j).Contains (rootPhase (544+j.val)) := by
  fin_cases j
  · exact IntegerRoots.root544_contains
  · exact IntegerRoots.root545_contains
  · exact IntegerRoots.root546_contains
  · exact IntegerRoots.root547_contains
  · exact IntegerRoots.root548_contains
  · exact IntegerRoots.root549_contains
  · exact IntegerRoots.root550_contains
  · exact IntegerRoots.root551_contains
  · exact IntegerRoots.root552_contains
  · exact IntegerRoots.root553_contains
  · exact IntegerRoots.root554_contains
  · exact IntegerRoots.root555_contains
  · exact IntegerRoots.root556_contains
  · exact IntegerRoots.root557_contains
  · exact IntegerRoots.root558_contains
  · exact IntegerRoots.root559_contains
  · exact IntegerRoots.root560_contains
  · exact IntegerRoots.root561_contains
  · exact IntegerRoots.root562_contains
  · exact IntegerRoots.root563_contains
  · exact IntegerRoots.root564_contains
  · exact IntegerRoots.root565_contains
  · exact IntegerRoots.root566_contains
  · exact IntegerRoots.root567_contains
  · exact IntegerRoots.root568_contains
  · exact IntegerRoots.root569_contains
  · exact IntegerRoots.root570_contains
  · exact IntegerRoots.root571_contains
  · exact IntegerRoots.root572_contains
  · exact IntegerRoots.root573_contains
  · exact IntegerRoots.root574_contains
  · exact IntegerRoots.root575_contains
def roots18 : Fin 32 → CBox := ![IntegerRoots.root576,IntegerRoots.root577,IntegerRoots.root578,IntegerRoots.root579,IntegerRoots.root580,IntegerRoots.root581,IntegerRoots.root582,IntegerRoots.root583,IntegerRoots.root584,IntegerRoots.root585,IntegerRoots.root586,IntegerRoots.root587,IntegerRoots.root588,IntegerRoots.root589,IntegerRoots.root590,IntegerRoots.root591,IntegerRoots.root592,IntegerRoots.root593,IntegerRoots.root594,IntegerRoots.root595,IntegerRoots.root596,IntegerRoots.root597,IntegerRoots.root598,IntegerRoots.root599,IntegerRoots.root600,IntegerRoots.root601,IntegerRoots.root602,IntegerRoots.root603,IntegerRoots.root604,IntegerRoots.root605,IntegerRoots.root606,IntegerRoots.root607]
lemma roots18_contains (j : Fin 32) : (roots18 j).Contains (rootPhase (576+j.val)) := by
  fin_cases j
  · exact IntegerRoots.root576_contains
  · exact IntegerRoots.root577_contains
  · exact IntegerRoots.root578_contains
  · exact IntegerRoots.root579_contains
  · exact IntegerRoots.root580_contains
  · exact IntegerRoots.root581_contains
  · exact IntegerRoots.root582_contains
  · exact IntegerRoots.root583_contains
  · exact IntegerRoots.root584_contains
  · exact IntegerRoots.root585_contains
  · exact IntegerRoots.root586_contains
  · exact IntegerRoots.root587_contains
  · exact IntegerRoots.root588_contains
  · exact IntegerRoots.root589_contains
  · exact IntegerRoots.root590_contains
  · exact IntegerRoots.root591_contains
  · exact IntegerRoots.root592_contains
  · exact IntegerRoots.root593_contains
  · exact IntegerRoots.root594_contains
  · exact IntegerRoots.root595_contains
  · exact IntegerRoots.root596_contains
  · exact IntegerRoots.root597_contains
  · exact IntegerRoots.root598_contains
  · exact IntegerRoots.root599_contains
  · exact IntegerRoots.root600_contains
  · exact IntegerRoots.root601_contains
  · exact IntegerRoots.root602_contains
  · exact IntegerRoots.root603_contains
  · exact IntegerRoots.root604_contains
  · exact IntegerRoots.root605_contains
  · exact IntegerRoots.root606_contains
  · exact IntegerRoots.root607_contains
def roots19 : Fin 32 → CBox := ![IntegerRoots.root608,IntegerRoots.root609,IntegerRoots.root610,IntegerRoots.root611,IntegerRoots.root612,IntegerRoots.root613,IntegerRoots.root614,IntegerRoots.root615,IntegerRoots.root616,IntegerRoots.root617,IntegerRoots.root618,IntegerRoots.root619,IntegerRoots.root620,IntegerRoots.root621,IntegerRoots.root622,IntegerRoots.root623,IntegerRoots.root624,IntegerRoots.root625,IntegerRoots.root626,IntegerRoots.root627,IntegerRoots.root628,IntegerRoots.root629,IntegerRoots.root630,IntegerRoots.root631,IntegerRoots.root632,IntegerRoots.root633,IntegerRoots.root634,IntegerRoots.root635,IntegerRoots.root636,IntegerRoots.root637,IntegerRoots.root638,IntegerRoots.root639]
lemma roots19_contains (j : Fin 32) : (roots19 j).Contains (rootPhase (608+j.val)) := by
  fin_cases j
  · exact IntegerRoots.root608_contains
  · exact IntegerRoots.root609_contains
  · exact IntegerRoots.root610_contains
  · exact IntegerRoots.root611_contains
  · exact IntegerRoots.root612_contains
  · exact IntegerRoots.root613_contains
  · exact IntegerRoots.root614_contains
  · exact IntegerRoots.root615_contains
  · exact IntegerRoots.root616_contains
  · exact IntegerRoots.root617_contains
  · exact IntegerRoots.root618_contains
  · exact IntegerRoots.root619_contains
  · exact IntegerRoots.root620_contains
  · exact IntegerRoots.root621_contains
  · exact IntegerRoots.root622_contains
  · exact IntegerRoots.root623_contains
  · exact IntegerRoots.root624_contains
  · exact IntegerRoots.root625_contains
  · exact IntegerRoots.root626_contains
  · exact IntegerRoots.root627_contains
  · exact IntegerRoots.root628_contains
  · exact IntegerRoots.root629_contains
  · exact IntegerRoots.root630_contains
  · exact IntegerRoots.root631_contains
  · exact IntegerRoots.root632_contains
  · exact IntegerRoots.root633_contains
  · exact IntegerRoots.root634_contains
  · exact IntegerRoots.root635_contains
  · exact IntegerRoots.root636_contains
  · exact IntegerRoots.root637_contains
  · exact IntegerRoots.root638_contains
  · exact IntegerRoots.root639_contains
def roots20 : Fin 32 → CBox := ![IntegerRoots.root640,IntegerRoots.root641,IntegerRoots.root642,IntegerRoots.root643,IntegerRoots.root644,IntegerRoots.root645,IntegerRoots.root646,IntegerRoots.root647,IntegerRoots.root648,IntegerRoots.root649,IntegerRoots.root650,IntegerRoots.root651,IntegerRoots.root652,IntegerRoots.root653,IntegerRoots.root654,IntegerRoots.root655,IntegerRoots.root656,IntegerRoots.root657,IntegerRoots.root658,IntegerRoots.root659,IntegerRoots.root660,IntegerRoots.root661,IntegerRoots.root662,IntegerRoots.root663,IntegerRoots.root664,IntegerRoots.root665,IntegerRoots.root666,IntegerRoots.root667,IntegerRoots.root668,IntegerRoots.root669,IntegerRoots.root670,IntegerRoots.root671]
lemma roots20_contains (j : Fin 32) : (roots20 j).Contains (rootPhase (640+j.val)) := by
  fin_cases j
  · exact IntegerRoots.root640_contains
  · exact IntegerRoots.root641_contains
  · exact IntegerRoots.root642_contains
  · exact IntegerRoots.root643_contains
  · exact IntegerRoots.root644_contains
  · exact IntegerRoots.root645_contains
  · exact IntegerRoots.root646_contains
  · exact IntegerRoots.root647_contains
  · exact IntegerRoots.root648_contains
  · exact IntegerRoots.root649_contains
  · exact IntegerRoots.root650_contains
  · exact IntegerRoots.root651_contains
  · exact IntegerRoots.root652_contains
  · exact IntegerRoots.root653_contains
  · exact IntegerRoots.root654_contains
  · exact IntegerRoots.root655_contains
  · exact IntegerRoots.root656_contains
  · exact IntegerRoots.root657_contains
  · exact IntegerRoots.root658_contains
  · exact IntegerRoots.root659_contains
  · exact IntegerRoots.root660_contains
  · exact IntegerRoots.root661_contains
  · exact IntegerRoots.root662_contains
  · exact IntegerRoots.root663_contains
  · exact IntegerRoots.root664_contains
  · exact IntegerRoots.root665_contains
  · exact IntegerRoots.root666_contains
  · exact IntegerRoots.root667_contains
  · exact IntegerRoots.root668_contains
  · exact IntegerRoots.root669_contains
  · exact IntegerRoots.root670_contains
  · exact IntegerRoots.root671_contains
def roots21 : Fin 32 → CBox := ![IntegerRoots.root672,IntegerRoots.root673,IntegerRoots.root674,IntegerRoots.root675,IntegerRoots.root676,IntegerRoots.root677,IntegerRoots.root678,IntegerRoots.root679,IntegerRoots.root680,IntegerRoots.root681,IntegerRoots.root682,IntegerRoots.root683,IntegerRoots.root684,IntegerRoots.root685,IntegerRoots.root686,IntegerRoots.root687,IntegerRoots.root688,IntegerRoots.root689,IntegerRoots.root690,IntegerRoots.root691,IntegerRoots.root692,IntegerRoots.root693,IntegerRoots.root694,IntegerRoots.root695,IntegerRoots.root696,IntegerRoots.root697,IntegerRoots.root698,IntegerRoots.root699,IntegerRoots.root700,IntegerRoots.root701,IntegerRoots.root702,IntegerRoots.root703]
lemma roots21_contains (j : Fin 32) : (roots21 j).Contains (rootPhase (672+j.val)) := by
  fin_cases j
  · exact IntegerRoots.root672_contains
  · exact IntegerRoots.root673_contains
  · exact IntegerRoots.root674_contains
  · exact IntegerRoots.root675_contains
  · exact IntegerRoots.root676_contains
  · exact IntegerRoots.root677_contains
  · exact IntegerRoots.root678_contains
  · exact IntegerRoots.root679_contains
  · exact IntegerRoots.root680_contains
  · exact IntegerRoots.root681_contains
  · exact IntegerRoots.root682_contains
  · exact IntegerRoots.root683_contains
  · exact IntegerRoots.root684_contains
  · exact IntegerRoots.root685_contains
  · exact IntegerRoots.root686_contains
  · exact IntegerRoots.root687_contains
  · exact IntegerRoots.root688_contains
  · exact IntegerRoots.root689_contains
  · exact IntegerRoots.root690_contains
  · exact IntegerRoots.root691_contains
  · exact IntegerRoots.root692_contains
  · exact IntegerRoots.root693_contains
  · exact IntegerRoots.root694_contains
  · exact IntegerRoots.root695_contains
  · exact IntegerRoots.root696_contains
  · exact IntegerRoots.root697_contains
  · exact IntegerRoots.root698_contains
  · exact IntegerRoots.root699_contains
  · exact IntegerRoots.root700_contains
  · exact IntegerRoots.root701_contains
  · exact IntegerRoots.root702_contains
  · exact IntegerRoots.root703_contains
def roots22 : Fin 32 → CBox := ![IntegerRoots.root704,IntegerRoots.root705,IntegerRoots.root706,IntegerRoots.root707,IntegerRoots.root708,IntegerRoots.root709,IntegerRoots.root710,IntegerRoots.root711,IntegerRoots.root712,IntegerRoots.root713,IntegerRoots.root714,IntegerRoots.root715,IntegerRoots.root716,IntegerRoots.root717,IntegerRoots.root718,IntegerRoots.root719,IntegerRoots.root720,IntegerRoots.root721,IntegerRoots.root722,IntegerRoots.root723,IntegerRoots.root724,IntegerRoots.root725,IntegerRoots.root726,IntegerRoots.root727,IntegerRoots.root728,IntegerRoots.root729,IntegerRoots.root730,IntegerRoots.root731,IntegerRoots.root732,IntegerRoots.root733,IntegerRoots.root734,IntegerRoots.root735]
lemma roots22_contains (j : Fin 32) : (roots22 j).Contains (rootPhase (704+j.val)) := by
  fin_cases j
  · exact IntegerRoots.root704_contains
  · exact IntegerRoots.root705_contains
  · exact IntegerRoots.root706_contains
  · exact IntegerRoots.root707_contains
  · exact IntegerRoots.root708_contains
  · exact IntegerRoots.root709_contains
  · exact IntegerRoots.root710_contains
  · exact IntegerRoots.root711_contains
  · exact IntegerRoots.root712_contains
  · exact IntegerRoots.root713_contains
  · exact IntegerRoots.root714_contains
  · exact IntegerRoots.root715_contains
  · exact IntegerRoots.root716_contains
  · exact IntegerRoots.root717_contains
  · exact IntegerRoots.root718_contains
  · exact IntegerRoots.root719_contains
  · exact IntegerRoots.root720_contains
  · exact IntegerRoots.root721_contains
  · exact IntegerRoots.root722_contains
  · exact IntegerRoots.root723_contains
  · exact IntegerRoots.root724_contains
  · exact IntegerRoots.root725_contains
  · exact IntegerRoots.root726_contains
  · exact IntegerRoots.root727_contains
  · exact IntegerRoots.root728_contains
  · exact IntegerRoots.root729_contains
  · exact IntegerRoots.root730_contains
  · exact IntegerRoots.root731_contains
  · exact IntegerRoots.root732_contains
  · exact IntegerRoots.root733_contains
  · exact IntegerRoots.root734_contains
  · exact IntegerRoots.root735_contains
def roots23 : Fin 32 → CBox := ![IntegerRoots.root736,IntegerRoots.root737,IntegerRoots.root738,IntegerRoots.root739,IntegerRoots.root740,IntegerRoots.root741,IntegerRoots.root742,IntegerRoots.root743,IntegerRoots.root744,IntegerRoots.root745,IntegerRoots.root746,IntegerRoots.root747,IntegerRoots.root748,IntegerRoots.root749,IntegerRoots.root750,IntegerRoots.root751,IntegerRoots.root752,IntegerRoots.root753,IntegerRoots.root754,IntegerRoots.root755,IntegerRoots.root756,IntegerRoots.root757,IntegerRoots.root758,IntegerRoots.root759,IntegerRoots.root760,IntegerRoots.root761,IntegerRoots.root762,IntegerRoots.root763,IntegerRoots.root764,IntegerRoots.root765,IntegerRoots.root766,IntegerRoots.root767]
lemma roots23_contains (j : Fin 32) : (roots23 j).Contains (rootPhase (736+j.val)) := by
  fin_cases j
  · exact IntegerRoots.root736_contains
  · exact IntegerRoots.root737_contains
  · exact IntegerRoots.root738_contains
  · exact IntegerRoots.root739_contains
  · exact IntegerRoots.root740_contains
  · exact IntegerRoots.root741_contains
  · exact IntegerRoots.root742_contains
  · exact IntegerRoots.root743_contains
  · exact IntegerRoots.root744_contains
  · exact IntegerRoots.root745_contains
  · exact IntegerRoots.root746_contains
  · exact IntegerRoots.root747_contains
  · exact IntegerRoots.root748_contains
  · exact IntegerRoots.root749_contains
  · exact IntegerRoots.root750_contains
  · exact IntegerRoots.root751_contains
  · exact IntegerRoots.root752_contains
  · exact IntegerRoots.root753_contains
  · exact IntegerRoots.root754_contains
  · exact IntegerRoots.root755_contains
  · exact IntegerRoots.root756_contains
  · exact IntegerRoots.root757_contains
  · exact IntegerRoots.root758_contains
  · exact IntegerRoots.root759_contains
  · exact IntegerRoots.root760_contains
  · exact IntegerRoots.root761_contains
  · exact IntegerRoots.root762_contains
  · exact IntegerRoots.root763_contains
  · exact IntegerRoots.root764_contains
  · exact IntegerRoots.root765_contains
  · exact IntegerRoots.root766_contains
  · exact IntegerRoots.root767_contains
def roots24 : Fin 32 → CBox := ![IntegerRoots.root768,IntegerRoots.root769,IntegerRoots.root770,IntegerRoots.root771,IntegerRoots.root772,IntegerRoots.root773,IntegerRoots.root774,IntegerRoots.root775,IntegerRoots.root776,IntegerRoots.root777,IntegerRoots.root778,IntegerRoots.root779,IntegerRoots.root780,IntegerRoots.root781,IntegerRoots.root782,IntegerRoots.root783,IntegerRoots.root784,IntegerRoots.root785,IntegerRoots.root786,IntegerRoots.root787,IntegerRoots.root788,IntegerRoots.root789,IntegerRoots.root790,IntegerRoots.root791,IntegerRoots.root792,IntegerRoots.root793,IntegerRoots.root794,IntegerRoots.root795,IntegerRoots.root796,IntegerRoots.root797,IntegerRoots.root798,IntegerRoots.root799]
lemma roots24_contains (j : Fin 32) : (roots24 j).Contains (rootPhase (768+j.val)) := by
  fin_cases j
  · exact IntegerRoots.root768_contains
  · exact IntegerRoots.root769_contains
  · exact IntegerRoots.root770_contains
  · exact IntegerRoots.root771_contains
  · exact IntegerRoots.root772_contains
  · exact IntegerRoots.root773_contains
  · exact IntegerRoots.root774_contains
  · exact IntegerRoots.root775_contains
  · exact IntegerRoots.root776_contains
  · exact IntegerRoots.root777_contains
  · exact IntegerRoots.root778_contains
  · exact IntegerRoots.root779_contains
  · exact IntegerRoots.root780_contains
  · exact IntegerRoots.root781_contains
  · exact IntegerRoots.root782_contains
  · exact IntegerRoots.root783_contains
  · exact IntegerRoots.root784_contains
  · exact IntegerRoots.root785_contains
  · exact IntegerRoots.root786_contains
  · exact IntegerRoots.root787_contains
  · exact IntegerRoots.root788_contains
  · exact IntegerRoots.root789_contains
  · exact IntegerRoots.root790_contains
  · exact IntegerRoots.root791_contains
  · exact IntegerRoots.root792_contains
  · exact IntegerRoots.root793_contains
  · exact IntegerRoots.root794_contains
  · exact IntegerRoots.root795_contains
  · exact IntegerRoots.root796_contains
  · exact IntegerRoots.root797_contains
  · exact IntegerRoots.root798_contains
  · exact IntegerRoots.root799_contains
def roots25 : Fin 32 → CBox := ![IntegerRoots.root800,IntegerRoots.root801,IntegerRoots.root802,IntegerRoots.root803,IntegerRoots.root804,IntegerRoots.root805,IntegerRoots.root806,IntegerRoots.root807,IntegerRoots.root808,IntegerRoots.root809,IntegerRoots.root810,IntegerRoots.root811,IntegerRoots.root812,IntegerRoots.root813,IntegerRoots.root814,IntegerRoots.root815,IntegerRoots.root816,IntegerRoots.root817,IntegerRoots.root818,IntegerRoots.root819,IntegerRoots.root820,IntegerRoots.root821,IntegerRoots.root822,IntegerRoots.root823,IntegerRoots.root824,IntegerRoots.root825,IntegerRoots.root826,IntegerRoots.root827,IntegerRoots.root828,IntegerRoots.root829,IntegerRoots.root830,IntegerRoots.root831]
lemma roots25_contains (j : Fin 32) : (roots25 j).Contains (rootPhase (800+j.val)) := by
  fin_cases j
  · exact IntegerRoots.root800_contains
  · exact IntegerRoots.root801_contains
  · exact IntegerRoots.root802_contains
  · exact IntegerRoots.root803_contains
  · exact IntegerRoots.root804_contains
  · exact IntegerRoots.root805_contains
  · exact IntegerRoots.root806_contains
  · exact IntegerRoots.root807_contains
  · exact IntegerRoots.root808_contains
  · exact IntegerRoots.root809_contains
  · exact IntegerRoots.root810_contains
  · exact IntegerRoots.root811_contains
  · exact IntegerRoots.root812_contains
  · exact IntegerRoots.root813_contains
  · exact IntegerRoots.root814_contains
  · exact IntegerRoots.root815_contains
  · exact IntegerRoots.root816_contains
  · exact IntegerRoots.root817_contains
  · exact IntegerRoots.root818_contains
  · exact IntegerRoots.root819_contains
  · exact IntegerRoots.root820_contains
  · exact IntegerRoots.root821_contains
  · exact IntegerRoots.root822_contains
  · exact IntegerRoots.root823_contains
  · exact IntegerRoots.root824_contains
  · exact IntegerRoots.root825_contains
  · exact IntegerRoots.root826_contains
  · exact IntegerRoots.root827_contains
  · exact IntegerRoots.root828_contains
  · exact IntegerRoots.root829_contains
  · exact IntegerRoots.root830_contains
  · exact IntegerRoots.root831_contains
def roots26 : Fin 32 → CBox := ![IntegerRoots.root832,IntegerRoots.root833,IntegerRoots.root834,IntegerRoots.root835,IntegerRoots.root836,IntegerRoots.root837,IntegerRoots.root838,IntegerRoots.root839,IntegerRoots.root840,IntegerRoots.root841,IntegerRoots.root842,IntegerRoots.root843,IntegerRoots.root844,IntegerRoots.root845,IntegerRoots.root846,IntegerRoots.root847,IntegerRoots.root848,IntegerRoots.root849,IntegerRoots.root850,IntegerRoots.root851,IntegerRoots.root852,IntegerRoots.root853,IntegerRoots.root854,IntegerRoots.root855,IntegerRoots.root856,IntegerRoots.root857,IntegerRoots.root858,IntegerRoots.root859,IntegerRoots.root860,IntegerRoots.root861,IntegerRoots.root862,IntegerRoots.root863]
lemma roots26_contains (j : Fin 32) : (roots26 j).Contains (rootPhase (832+j.val)) := by
  fin_cases j
  · exact IntegerRoots.root832_contains
  · exact IntegerRoots.root833_contains
  · exact IntegerRoots.root834_contains
  · exact IntegerRoots.root835_contains
  · exact IntegerRoots.root836_contains
  · exact IntegerRoots.root837_contains
  · exact IntegerRoots.root838_contains
  · exact IntegerRoots.root839_contains
  · exact IntegerRoots.root840_contains
  · exact IntegerRoots.root841_contains
  · exact IntegerRoots.root842_contains
  · exact IntegerRoots.root843_contains
  · exact IntegerRoots.root844_contains
  · exact IntegerRoots.root845_contains
  · exact IntegerRoots.root846_contains
  · exact IntegerRoots.root847_contains
  · exact IntegerRoots.root848_contains
  · exact IntegerRoots.root849_contains
  · exact IntegerRoots.root850_contains
  · exact IntegerRoots.root851_contains
  · exact IntegerRoots.root852_contains
  · exact IntegerRoots.root853_contains
  · exact IntegerRoots.root854_contains
  · exact IntegerRoots.root855_contains
  · exact IntegerRoots.root856_contains
  · exact IntegerRoots.root857_contains
  · exact IntegerRoots.root858_contains
  · exact IntegerRoots.root859_contains
  · exact IntegerRoots.root860_contains
  · exact IntegerRoots.root861_contains
  · exact IntegerRoots.root862_contains
  · exact IntegerRoots.root863_contains
def roots27 : Fin 32 → CBox := ![IntegerRoots.root864,IntegerRoots.root865,IntegerRoots.root866,IntegerRoots.root867,IntegerRoots.root868,IntegerRoots.root869,IntegerRoots.root870,IntegerRoots.root871,IntegerRoots.root872,IntegerRoots.root873,IntegerRoots.root874,IntegerRoots.root875,IntegerRoots.root876,IntegerRoots.root877,IntegerRoots.root878,IntegerRoots.root879,IntegerRoots.root880,IntegerRoots.root881,IntegerRoots.root882,IntegerRoots.root883,IntegerRoots.root884,IntegerRoots.root885,IntegerRoots.root886,IntegerRoots.root887,IntegerRoots.root888,IntegerRoots.root889,IntegerRoots.root890,IntegerRoots.root891,IntegerRoots.root892,IntegerRoots.root893,IntegerRoots.root894,IntegerRoots.root895]
lemma roots27_contains (j : Fin 32) : (roots27 j).Contains (rootPhase (864+j.val)) := by
  fin_cases j
  · exact IntegerRoots.root864_contains
  · exact IntegerRoots.root865_contains
  · exact IntegerRoots.root866_contains
  · exact IntegerRoots.root867_contains
  · exact IntegerRoots.root868_contains
  · exact IntegerRoots.root869_contains
  · exact IntegerRoots.root870_contains
  · exact IntegerRoots.root871_contains
  · exact IntegerRoots.root872_contains
  · exact IntegerRoots.root873_contains
  · exact IntegerRoots.root874_contains
  · exact IntegerRoots.root875_contains
  · exact IntegerRoots.root876_contains
  · exact IntegerRoots.root877_contains
  · exact IntegerRoots.root878_contains
  · exact IntegerRoots.root879_contains
  · exact IntegerRoots.root880_contains
  · exact IntegerRoots.root881_contains
  · exact IntegerRoots.root882_contains
  · exact IntegerRoots.root883_contains
  · exact IntegerRoots.root884_contains
  · exact IntegerRoots.root885_contains
  · exact IntegerRoots.root886_contains
  · exact IntegerRoots.root887_contains
  · exact IntegerRoots.root888_contains
  · exact IntegerRoots.root889_contains
  · exact IntegerRoots.root890_contains
  · exact IntegerRoots.root891_contains
  · exact IntegerRoots.root892_contains
  · exact IntegerRoots.root893_contains
  · exact IntegerRoots.root894_contains
  · exact IntegerRoots.root895_contains
def roots28 : Fin 32 → CBox := ![IntegerRoots.root896,IntegerRoots.root897,IntegerRoots.root898,IntegerRoots.root899,IntegerRoots.root900,IntegerRoots.root901,IntegerRoots.root902,IntegerRoots.root903,IntegerRoots.root904,IntegerRoots.root905,IntegerRoots.root906,IntegerRoots.root907,IntegerRoots.root908,IntegerRoots.root909,IntegerRoots.root910,IntegerRoots.root911,IntegerRoots.root912,IntegerRoots.root913,IntegerRoots.root914,IntegerRoots.root915,IntegerRoots.root916,IntegerRoots.root917,IntegerRoots.root918,IntegerRoots.root919,IntegerRoots.root920,IntegerRoots.root921,IntegerRoots.root922,IntegerRoots.root923,IntegerRoots.root924,IntegerRoots.root925,IntegerRoots.root926,IntegerRoots.root927]
lemma roots28_contains (j : Fin 32) : (roots28 j).Contains (rootPhase (896+j.val)) := by
  fin_cases j
  · exact IntegerRoots.root896_contains
  · exact IntegerRoots.root897_contains
  · exact IntegerRoots.root898_contains
  · exact IntegerRoots.root899_contains
  · exact IntegerRoots.root900_contains
  · exact IntegerRoots.root901_contains
  · exact IntegerRoots.root902_contains
  · exact IntegerRoots.root903_contains
  · exact IntegerRoots.root904_contains
  · exact IntegerRoots.root905_contains
  · exact IntegerRoots.root906_contains
  · exact IntegerRoots.root907_contains
  · exact IntegerRoots.root908_contains
  · exact IntegerRoots.root909_contains
  · exact IntegerRoots.root910_contains
  · exact IntegerRoots.root911_contains
  · exact IntegerRoots.root912_contains
  · exact IntegerRoots.root913_contains
  · exact IntegerRoots.root914_contains
  · exact IntegerRoots.root915_contains
  · exact IntegerRoots.root916_contains
  · exact IntegerRoots.root917_contains
  · exact IntegerRoots.root918_contains
  · exact IntegerRoots.root919_contains
  · exact IntegerRoots.root920_contains
  · exact IntegerRoots.root921_contains
  · exact IntegerRoots.root922_contains
  · exact IntegerRoots.root923_contains
  · exact IntegerRoots.root924_contains
  · exact IntegerRoots.root925_contains
  · exact IntegerRoots.root926_contains
  · exact IntegerRoots.root927_contains
def roots29 : Fin 32 → CBox := ![IntegerRoots.root928,IntegerRoots.root929,IntegerRoots.root930,IntegerRoots.root931,IntegerRoots.root932,IntegerRoots.root933,IntegerRoots.root934,IntegerRoots.root935,IntegerRoots.root936,IntegerRoots.root937,IntegerRoots.root938,IntegerRoots.root939,IntegerRoots.root940,IntegerRoots.root941,IntegerRoots.root942,IntegerRoots.root943,IntegerRoots.root944,IntegerRoots.root945,IntegerRoots.root946,IntegerRoots.root947,IntegerRoots.root948,IntegerRoots.root949,IntegerRoots.root950,IntegerRoots.root951,IntegerRoots.root952,IntegerRoots.root953,IntegerRoots.root954,IntegerRoots.root955,IntegerRoots.root956,IntegerRoots.root957,IntegerRoots.root958,IntegerRoots.root959]
lemma roots29_contains (j : Fin 32) : (roots29 j).Contains (rootPhase (928+j.val)) := by
  fin_cases j
  · exact IntegerRoots.root928_contains
  · exact IntegerRoots.root929_contains
  · exact IntegerRoots.root930_contains
  · exact IntegerRoots.root931_contains
  · exact IntegerRoots.root932_contains
  · exact IntegerRoots.root933_contains
  · exact IntegerRoots.root934_contains
  · exact IntegerRoots.root935_contains
  · exact IntegerRoots.root936_contains
  · exact IntegerRoots.root937_contains
  · exact IntegerRoots.root938_contains
  · exact IntegerRoots.root939_contains
  · exact IntegerRoots.root940_contains
  · exact IntegerRoots.root941_contains
  · exact IntegerRoots.root942_contains
  · exact IntegerRoots.root943_contains
  · exact IntegerRoots.root944_contains
  · exact IntegerRoots.root945_contains
  · exact IntegerRoots.root946_contains
  · exact IntegerRoots.root947_contains
  · exact IntegerRoots.root948_contains
  · exact IntegerRoots.root949_contains
  · exact IntegerRoots.root950_contains
  · exact IntegerRoots.root951_contains
  · exact IntegerRoots.root952_contains
  · exact IntegerRoots.root953_contains
  · exact IntegerRoots.root954_contains
  · exact IntegerRoots.root955_contains
  · exact IntegerRoots.root956_contains
  · exact IntegerRoots.root957_contains
  · exact IntegerRoots.root958_contains
  · exact IntegerRoots.root959_contains
def roots30 : Fin 32 → CBox := ![IntegerRoots.root960,IntegerRoots.root961,IntegerRoots.root962,IntegerRoots.root963,IntegerRoots.root964,IntegerRoots.root965,IntegerRoots.root966,IntegerRoots.root967,IntegerRoots.root968,IntegerRoots.root969,IntegerRoots.root970,IntegerRoots.root971,IntegerRoots.root972,IntegerRoots.root973,IntegerRoots.root974,IntegerRoots.root975,IntegerRoots.root976,IntegerRoots.root977,IntegerRoots.root978,IntegerRoots.root979,IntegerRoots.root980,IntegerRoots.root981,IntegerRoots.root982,IntegerRoots.root983,IntegerRoots.root984,IntegerRoots.root985,IntegerRoots.root986,IntegerRoots.root987,IntegerRoots.root988,IntegerRoots.root989,IntegerRoots.root990,IntegerRoots.root991]
lemma roots30_contains (j : Fin 32) : (roots30 j).Contains (rootPhase (960+j.val)) := by
  fin_cases j
  · exact IntegerRoots.root960_contains
  · exact IntegerRoots.root961_contains
  · exact IntegerRoots.root962_contains
  · exact IntegerRoots.root963_contains
  · exact IntegerRoots.root964_contains
  · exact IntegerRoots.root965_contains
  · exact IntegerRoots.root966_contains
  · exact IntegerRoots.root967_contains
  · exact IntegerRoots.root968_contains
  · exact IntegerRoots.root969_contains
  · exact IntegerRoots.root970_contains
  · exact IntegerRoots.root971_contains
  · exact IntegerRoots.root972_contains
  · exact IntegerRoots.root973_contains
  · exact IntegerRoots.root974_contains
  · exact IntegerRoots.root975_contains
  · exact IntegerRoots.root976_contains
  · exact IntegerRoots.root977_contains
  · exact IntegerRoots.root978_contains
  · exact IntegerRoots.root979_contains
  · exact IntegerRoots.root980_contains
  · exact IntegerRoots.root981_contains
  · exact IntegerRoots.root982_contains
  · exact IntegerRoots.root983_contains
  · exact IntegerRoots.root984_contains
  · exact IntegerRoots.root985_contains
  · exact IntegerRoots.root986_contains
  · exact IntegerRoots.root987_contains
  · exact IntegerRoots.root988_contains
  · exact IntegerRoots.root989_contains
  · exact IntegerRoots.root990_contains
  · exact IntegerRoots.root991_contains
def roots31 : Fin 32 → CBox := ![IntegerRoots.root992,IntegerRoots.root993,IntegerRoots.root994,IntegerRoots.root995,IntegerRoots.root996,IntegerRoots.root997,IntegerRoots.root998,IntegerRoots.root999,IntegerRoots.root1000,IntegerRoots.root1001,IntegerRoots.root1002,IntegerRoots.root1003,IntegerRoots.root1004,IntegerRoots.root1005,IntegerRoots.root1006,IntegerRoots.root1007,IntegerRoots.root1008,IntegerRoots.root1009,IntegerRoots.root1010,IntegerRoots.root1011,IntegerRoots.root1012,IntegerRoots.root1013,IntegerRoots.root1014,IntegerRoots.root1015,IntegerRoots.root1016,IntegerRoots.root1017,IntegerRoots.root1018,IntegerRoots.root1019,IntegerRoots.root1020,IntegerRoots.root1021,IntegerRoots.root1022,IntegerRoots.root1023]
lemma roots31_contains (j : Fin 32) : (roots31 j).Contains (rootPhase (992+j.val)) := by
  fin_cases j
  · exact IntegerRoots.root992_contains
  · exact IntegerRoots.root993_contains
  · exact IntegerRoots.root994_contains
  · exact IntegerRoots.root995_contains
  · exact IntegerRoots.root996_contains
  · exact IntegerRoots.root997_contains
  · exact IntegerRoots.root998_contains
  · exact IntegerRoots.root999_contains
  · exact IntegerRoots.root1000_contains
  · exact IntegerRoots.root1001_contains
  · exact IntegerRoots.root1002_contains
  · exact IntegerRoots.root1003_contains
  · exact IntegerRoots.root1004_contains
  · exact IntegerRoots.root1005_contains
  · exact IntegerRoots.root1006_contains
  · exact IntegerRoots.root1007_contains
  · exact IntegerRoots.root1008_contains
  · exact IntegerRoots.root1009_contains
  · exact IntegerRoots.root1010_contains
  · exact IntegerRoots.root1011_contains
  · exact IntegerRoots.root1012_contains
  · exact IntegerRoots.root1013_contains
  · exact IntegerRoots.root1014_contains
  · exact IntegerRoots.root1015_contains
  · exact IntegerRoots.root1016_contains
  · exact IntegerRoots.root1017_contains
  · exact IntegerRoots.root1018_contains
  · exact IntegerRoots.root1019_contains
  · exact IntegerRoots.root1020_contains
  · exact IntegerRoots.root1021_contains
  · exact IntegerRoots.root1022_contains
  · exact IntegerRoots.root1023_contains
def rootRows : Fin 32 → Fin 32 → CBox := ![roots0,roots1,roots2,roots3,roots4,roots5,roots6,roots7,roots8,roots9,roots10,roots11,roots12,roots13,roots14,roots15,roots16,roots17,roots18,roots19,roots20,roots21,roots22,roots23,roots24,roots25,roots26,roots27,roots28,roots29,roots30,roots31]
lemma rootRows_contains (i j : Fin 32) : (rootRows i j).Contains (rootPhase (32*i.val+j.val)) := by
  fin_cases i
  · exact roots0_contains j
  · exact roots1_contains j
  · exact roots2_contains j
  · exact roots3_contains j
  · exact roots4_contains j
  · exact roots5_contains j
  · exact roots6_contains j
  · exact roots7_contains j
  · exact roots8_contains j
  · exact roots9_contains j
  · exact roots10_contains j
  · exact roots11_contains j
  · exact roots12_contains j
  · exact roots13_contains j
  · exact roots14_contains j
  · exact roots15_contains j
  · exact roots16_contains j
  · exact roots17_contains j
  · exact roots18_contains j
  · exact roots19_contains j
  · exact roots20_contains j
  · exact roots21_contains j
  · exact roots22_contains j
  · exact roots23_contains j
  · exact roots24_contains j
  · exact roots25_contains j
  · exact roots26_contains j
  · exact roots27_contains j
  · exact roots28_contains j
  · exact roots29_contains j
  · exact roots30_contains j
  · exact roots31_contains j
def rootLookup (n : ℕ) : CBox :=
  rootRows ⟨(n%1024)/32,by omega⟩ ⟨n%32,by omega⟩
lemma rootLookup_contains (n : ℕ) : (rootLookup n).Contains (rootPhase (n%1024)) := by
  have he : 32*((n%1024)/32)+n%32 = n%1024 := by omega
  simpa only [rootLookup,he] using rootRows_contains ⟨(n%1024)/32,by omega⟩ ⟨n%32,by omega⟩

def partialBox (v : ℕ) : ℕ → RBox
  | 0 => ⟨0,0⟩
  | N+1 => (partialBox v N).add ((rootLookup (2*(N+1)*(2*v+1))).re.scale 1
      (4*((N+1:ℕ):ℤ)^2-1))
lemma partialBox_contains (v N : ℕ) : (partialBox v N).Contains (fejerPartial v N) := by
  induction N with
  | zero => simp [partialBox,fejerPartial_zero,RBox.Contains]
  | succ N ih =>
    exact fejerPartial_checked_step v N _ _ _ _ ih
      (rootLookup_contains (2*(N+1)*(2*v+1))) rfl rfl

def weightBoxCalc (v : ℕ) : RBox :=
  ((RBox.rat 1 1).add ((partialBox v 127).scale (-2) 1)).scale 1 256
lemma weightBoxCalc_contains (v : ℕ) : (weightBoxCalc v).Contains (fejerWeight v) :=
  fejerWeight_checked v _ _ (partialBox_contains v 127) rfl

def weight0 : RBox := ⟨32854899021958510264571372,32854899021958510264684290⟩
lemma weight0_contains : weight0.Contains (fejerWeight 0) := by
  have he : weightBoxCalc 0 = weight0 := by decide +kernel
  rw [← he]
  exact weightBoxCalc_contains 0
def weight1 : RBox := ⟨115643890836329592300920991,115643890836329592301652707⟩
lemma weight1_contains : weight1.Contains (fejerWeight 1) := by
  have he : weightBoxCalc 1 = weight1 := by decide +kernel
  rw [← he]
  exact weightBoxCalc_contains 1
def weight2 : RBox := ⟨186425341186478142130637142,186425341186478142132071158⟩
lemma weight2_contains : weight2.Contains (fejerWeight 2) := by
  have he : weightBoxCalc 2 = weight2 := by decide +kernel
  rw [← he]
  exact weightBoxCalc_contains 2
def weight3 : RBox := ⟨264792628993592540896364518,264792628993592540898468111⟩
lemma weight3_contains : weight3.Contains (fejerWeight 3) := by
  have he : weightBoxCalc 3 = weight3 := by decide +kernel
  rw [← he]
  exact weightBoxCalc_contains 3
def weight4 : RBox := ⟨337625197927180191466743821,337625197927180191469520764⟩
lemma weight4_contains : weight4.Contains (fejerWeight 4) := by
  have he : weightBoxCalc 4 = weight4 := by decide +kernel
  rw [← he]
  exact weightBoxCalc_contains 4
def weight5 : RBox := ⟨414695778421447914954232494,414695778421447914957689225⟩
lemma weight5_contains : weight5.Contains (fejerWeight 5) := by
  have he : weightBoxCalc 5 = weight5 := by decide +kernel
  rw [← he]
  exact weightBoxCalc_contains 5
def weight6 : RBox := ⟨488189937000491145122329595,488189937000491145126467967⟩
lemma weight6_contains : weight6.Contains (fejerWeight 6) := by
  have he : weightBoxCalc 6 = weight6 := by decide +kernel
  rw [← he]
  exact weightBoxCalc_contains 6
def weight7 : RBox := ⟨564585313122083449406883548,564585313122083449411708570⟩
lemma weight7_contains : weight7.Contains (fejerWeight 7) := by
  have he : weightBoxCalc 7 = weight7 := by decide +kernel
  rw [← he]
  exact weightBoxCalc_contains 7
def weight8 : RBox := ⟨638317675207538393581834267,638317675207538393587343582⟩
lemma weight8_contains : weight8.Contains (fejerWeight 8) := by
  have he : weightBoxCalc 8 = weight8 := by decide +kernel
  rw [← he]
  exact weightBoxCalc_contains 8
def weight9 : RBox := ⟨714227765284898142560721054,714227765284898142566835076⟩
lemma weight9_contains : weight9.Contains (fejerWeight 9) := by
  have he : weightBoxCalc 9 = weight9 := by decide +kernel
  rw [← he]
  exact weightBoxCalc_contains 9
def weight10 : RBox := ⟨787997020780326835710053428,787997020780326835716892278⟩
lemma weight10_contains : weight10.Contains (fejerWeight 10) := by
  have he : weightBoxCalc 10 = weight10 := by decide +kernel
  rw [← he]
  exact weightBoxCalc_contains 10
def weight11 : RBox := ⟨863485783121840440251192337,863485783121840440258718471⟩
lemma weight11_contains : weight11.Contains (fejerWeight 11) := by
  have he : weightBoxCalc 11 = weight11 := by decide +kernel
  rw [← he]
  exact weightBoxCalc_contains 11
def weight12 : RBox := ⟨937167764013815150899287971,937167764013815150907451278⟩
lemma weight12_contains : weight12.Contains (fejerWeight 12) := by
  have he : weightBoxCalc 12 = weight12 := by decide +kernel
  rw [← he]
  exact weightBoxCalc_contains 12
def weight13 : RBox := ⟨1012249534291717575608623519,1012249534291717575617377085⟩
lemma weight13_contains : weight13.Contains (fejerWeight 13) := by
  have he : weightBoxCalc 13 = weight13 := by decide +kernel
  rw [← he]
  exact weightBoxCalc_contains 13
def weight14 : RBox := ⟨1085753824000420340315222767,1085753824000420340324713544⟩
lemma weight14_contains : weight14.Contains (fejerWeight 14) := by
  have he : weightBoxCalc 14 = weight14 := by decide +kernel
  rw [← he]
  exact weightBoxCalc_contains 14
def weight15 : RBox := ⟨1160419579996777923424081859,1160419579996777923434294798⟩
lemma weight15_contains : weight15.Contains (fejerWeight 15) := by
  have he : weightBoxCalc 15 = weight15 := by decide +kernel
  rw [← he]
  exact weightBoxCalc_contains 15
def weight16 : RBox := ⟨1233672901838719242063693439,1233672901838719242074583778⟩
lemma weight16_contains : weight16.Contains (fejerWeight 16) := by
  have he : weightBoxCalc 16 = weight16 := by decide +kernel
  rw [← he]
  exact weightBoxCalc_contains 16
def weight17 : RBox := ⟨1307901266852325226207371856,1307901266852325226218877348⟩
lemma weight17_contains : weight17.Contains (fejerWeight 17) := by
  have he : weightBoxCalc 17 = weight17 := by decide +kernel
  rw [← he]
  exact weightBoxCalc_contains 17
def weight18 : RBox := ⟨1380840026805233674564253760,1380840026805233674576336188⟩
lemma weight18_contains : weight18.Contains (fejerWeight 18) := by
  have he : weightBoxCalc 18 = weight18 := by decide +kernel
  rw [← he]
  exact weightBoxCalc_contains 18
def weight19 : RBox := ⟨1454602544552288260551142916,1454602544552288260564135431⟩
lemma weight19_contains : weight19.Contains (fejerWeight 19) := by
  have he : weightBoxCalc 19 = weight19 := by decide +kernel
  rw [← he]
  exact weightBoxCalc_contains 19
def weight20 : RBox := ⟨1527169088187803451402758321,1527169088187803451416235366⟩
lemma weight20_contains : weight20.Contains (fejerWeight 20) := by
  have he : weightBoxCalc 20 = weight20 := by decide +kernel
  rw [← he]
  exact weightBoxCalc_contains 20
def weight21 : RBox := ⟨1600433014992203402676425795,1600433014992203402690394316⟩
lemma weight21_contains : weight21.Contains (fejerWeight 21) := by
  have he : weightBoxCalc 21 = weight21 := by decide +kernel
  rw [← he]
  exact weightBoxCalc_contains 21
def weight22 : RBox := ⟨1672573587728020047536379128,1672573587728020047551275851⟩
lemma weight22_contains : weight22.Contains (fejerWeight 22) := by
  have he : weightBoxCalc 22 = weight22 := by decide +kernel
  rw [← he]
  exact weightBoxCalc_contains 22
def weight23 : RBox := ⟨1745303488581413123273844206,1745303488581413123289152695⟩
lemma weight23_contains : weight23.Contains (fejerWeight 23) := by
  have he : weightBoxCalc 23 = weight23 := by decide +kernel
  rw [← he]
  exact weightBoxCalc_contains 23
def weight24 : RBox := ⟨1816967052637353898950070577,1816967052637353898966224051⟩
lemma weight24_contains : weight24.Contains (fejerWeight 24) := by
  have he : weightBoxCalc 24 = weight24 := by decide +kernel
  rw [← he]
  exact weightBoxCalc_contains 24
def weight25 : RBox := ⟨1889125772053601543611958466,1889125772053601543629036949⟩
lemma weight25_contains : weight25.Contains (fejerWeight 25) := by
  have he : weightBoxCalc 25 = weight25 := by decide +kernel
  rw [← he]
  exact weightBoxCalc_contains 25
def weight26 : RBox := ⟨1960263286585925611396448845,1960263286585925611413821417⟩
lemma weight26_contains : weight26.Contains (fejerWeight 26) := by
  have he : weightBoxCalc 26 = weight26 := by decide +kernel
  rw [← he]
  exact weightBoxCalc_contains 26
def weight27 : RBox := ⟨2031812570769548302370422369,2031812570769548302388653767⟩
lemma weight27_contains : weight27.Contains (fejerWeight 27) := by
  have he : weightBoxCalc 27 = weight27 := by decide +kernel
  rw [← he]
  exact weightBoxCalc_contains 27
def weight28 : RBox := ⟨2102376537417226956261905336,2102376537417226956280224648⟩
lemma weight28_contains : weight28.Contains (fejerWeight 28) := by
  have he : weightBoxCalc 28 = weight28 := by decide +kernel
  rw [← he]
  exact weightBoxCalc_contains 28
def weight29 : RBox := ⟨2173277451385880597969454359,2173277451385880597988851991⟩
lemma weight29_contains : weight29.Contains (fejerWeight 29) := by
  have he : weightBoxCalc 29 = weight29 := by decide +kernel
  rw [← he]
  exact weightBoxCalc_contains 29
def weight30 : RBox := ⟨2243221619351013954728161609,2243221619351013954748284485⟩
lemma weight30_contains : weight30.Contains (fejerWeight 30) := by
  have he : weightBoxCalc 30 = weight30 := by decide +kernel
  rw [← he]
  exact weightBoxCalc_contains 30
def weight31 : RBox := ⟨2313434838032280323185484641,2313434838032280323206471113⟩
lemma weight31_contains : weight31.Contains (fejerWeight 31) := by
  have he : weightBoxCalc 31 = weight31 := by decide +kernel
  rw [← he]
  exact weightBoxCalc_contains 31
def weight32 : RBox := ⟨2382714008961423530853016570,2382714008961423530873945017⟩
lemma weight32_contains : weight32.Contains (fejerWeight 32) := by
  have he : weightBoxCalc 32 = weight32 := by decide +kernel
  rw [← he]
  exact weightBoxCalc_contains 32
def weight33 : RBox := ⟨2452200027868549999065623669,2452200027868549999087532266⟩
lemma weight33_contains : weight33.Contains (fejerWeight 33) := by
  have he : weightBoxCalc 33 = weight33 := by decide +kernel
  rw [← he]
  exact weightBoxCalc_contains 33
def weight34 : RBox := ⟨2520769925313023080757748879,2520769925313023080780476129⟩
lemma weight34_contains : weight34.Contains (fejerWeight 34) := by
  have he : weightBoxCalc 34 = weight34 := by decide +kernel
  rw [← he]
  exact weightBoxCalc_contains 34
def weight35 : RBox := ⟨2589489218210731982105629167,2589489218210731982129273601⟩
lemma weight35_contains : weight35.Contains (fejerWeight 35) := by
  have he : weightBoxCalc 35 = weight35 := by decide +kernel
  rw [← he]
  exact weightBoxCalc_contains 35
def weight36 : RBox := ⟨2657306400097242267236794690,2657306400097242267261517376⟩
lemma weight36_contains : weight36.Contains (fejerWeight 36) := by
  have he : weightBoxCalc 36 = weight36 := by decide +kernel
  rw [← he]
  exact weightBoxCalc_contains 36
def weight37 : RBox := ⟨2725219540718512429700730282,2725219540718512429724967257⟩
lemma weight37_contains : weight37.Contains (fejerWeight 37) := by
  have he : weightBoxCalc 37 = weight37 := by decide +kernel
  rw [← he]
  exact weightBoxCalc_contains 37
def weight38 : RBox := ⟨2792241341182642226017712775,2792241341182642226042794226⟩
lemma weight38_contains : weight38.Contains (fejerWeight 38) := by
  have he : weightBoxCalc 38 = weight38 := by decide +kernel
  rw [← he]
  exact weightBoxCalc_contains 38
def weight39 : RBox := ⟨2859309099941888586034171026,2859309099941888586059884613⟩
lemma weight39_contains : weight39.Contains (fejerWeight 39) := by
  have he : weightBoxCalc 39 = weight39 := by decide +kernel
  rw [← he]
  exact weightBoxCalc_contains 39
def weight40 : RBox := ⟨2925493591637947329143346558,2925493591637947329169901907⟩
lemma weight40_contains : weight40.Contains (fejerWeight 40) := by
  have he : weightBoxCalc 40 = weight40 := by decide +kernel
  rw [← he]
  exact weightBoxCalc_contains 40
def weight41 : RBox := ⟨2991677014551349386351111171,2991677014551349386378554997⟩
lemma weight41_contains : weight41.Contains (fejerWeight 41) := by
  have he : weightBoxCalc 41 = weight41 := by decide +kernel
  rw [← he]
  exact weightBoxCalc_contains 41
def weight42 : RBox := ⟨3056982985503579824197139599,3056982985503579824225456620⟩
lemma weight42_contains : weight42.Contains (fejerWeight 42) := by
  have he : weightBoxCalc 42 = weight42 := by decide +kernel
  rw [← he]
  exact weightBoxCalc_contains 42
def weight43 : RBox := ⟨3122243460179323820935372368,3122243460179323820962774638⟩
lemma weight43_contains : weight43.Contains (fejerWeight 43) := by
  have he : weightBoxCalc 43 = weight43 := by decide +kernel
  rw [← he]
  exact weightBoxCalc_contains 43
def weight44 : RBox := ⟨3186630401119962167500951173,3186630401119962167529518099⟩
lemma weight44_contains : weight44.Contains (fejerWeight 44) := by
  have he : weightBoxCalc 44 = weight44 := by decide +kernel
  rw [← he]
  exact weightBoxCalc_contains 44
def weight45 : RBox := ⟨3250929713166444687604013502,3250929713166444687633456753⟩
lemma weight45_contains : weight45.Contains (fejerWeight 45) := by
  have he : weightBoxCalc 45 = weight45 := by decide +kernel
  rw [← he]
  exact weightBoxCalc_contains 45
def weight46 : RBox := ⟨3314357812533848584803790568,3314357812533848584834344507⟩
lemma weight46_contains : weight46.Contains (fejerWeight 46) := by
  have he : weightBoxCalc 46 = weight46 := by decide +kernel
  rw [← he]
  exact weightBoxCalc_contains 46
def weight47 : RBox := ⟨3377658194733971570150282385,3377658194733971570181313304⟩
lemma weight47_contains : weight47.Contains (fejerWeight 47) := by
  have he : weightBoxCalc 47 = weight47 := by decide +kernel
  rw [← he]
  exact weightBoxCalc_contains 47
def weight48 : RBox := ⟨3440088339323272551877889125,3440088339323272551909791348⟩
lemma weight48_contains : weight48.Contains (fejerWeight 48) := by
  have he : weightBoxCalc 48 = weight48 := by decide +kernel
  rw [← he]
  exact weightBoxCalc_contains 48
def weight49 : RBox := ⟨3502352515249085836173697390,3502352515249085836206540493⟩
lemma weight49_contains : weight49.Contains (fejerWeight 49) := by
  have he : weightBoxCalc 49 = weight49 := by decide +kernel
  rw [← he]
  exact weightBoxCalc_contains 49
def weight50 : RBox := ⟨3563746295065386521636763529,3563746295065386521670600773⟩
lemma weight50_contains : weight50.Contains (fejerWeight 50) := by
  have he : weightBoxCalc 50 = weight50 := by decide +kernel
  rw [← he]
  exact weightBoxCalc_contains 50
def weight51 : RBox := ⟨3624937518344627753212409149,3624937518344627753244187615⟩
lemma weight51_contains : weight51.Contains (fejerWeight 51) := by
  have he : weightBoxCalc 51 = weight51 := by decide +kernel
  rw [← he]
  exact weightBoxCalc_contains 51
def weight52 : RBox := ⟨3685257234595085284362657313,3685257234595085284395643772⟩
lemma weight52_contains : weight52.Contains (fejerWeight 52) := by
  have he : weightBoxCalc 52 = weight52 := by decide +kernel
  rw [← he]
  exact weightBoxCalc_contains 52
def weight53 : RBox := ⟨3745339324718025582912840989,3745339324718025582946757593⟩
lemma weight53_contains : weight53.Contains (fejerWeight 53) := by
  have he : weightBoxCalc 53 = weight53 := by decide +kernel
  rw [← he]
  exact weightBoxCalc_contains 53
def weight54 : RBox := ⟨3804548000151240159002014035,3804548000151240159036827563⟩
lemma weight54_contains : weight54.Contains (fejerWeight 54) := by
  have he : weightBoxCalc 54 = weight54 := by decide +kernel
  rw [← he]
  exact weightBoxCalc_contains 54
def weight55 : RBox := ⟨3863485375477059329230206922,3863485375477059329265775521⟩
lemma weight55_contains : weight55.Contains (fejerWeight 55) := by
  have he : weightBoxCalc 55 = weight55 := by decide +kernel
  rw [← he]
  exact weightBoxCalc_contains 55
def weight56 : RBox := ⟨3921546766472693407786744533,3921546766472693407823247213⟩
lemma weight56_contains : weight56.Contains (fejerWeight 56) := by
  have he : weightBoxCalc 56 = weight56 := by decide +kernel
  rw [← he]
  exact weightBoxCalc_contains 56
def weight57 : RBox := ⟨3979304474929752085786739772,3979304474929752085823420507⟩
lemma weight57_contains : weight57.Contains (fejerWeight 57) := by
  have he : weightBoxCalc 57 = weight57 := by decide +kernel
  rw [← he]
  exact weightBoxCalc_contains 57
def weight58 : RBox := ⟨4036183084882287367011186813,4036183084882287367048768249⟩
lemma weight58_contains : weight58.Contains (fejerWeight 58) := by
  have he : weightBoxCalc 58 = weight58 := by decide +kernel
  rw [← he]
  exact weightBoxCalc_contains 58
def weight59 : RBox := ⟨4092726832736535951842881697,4092726832736535951881047303⟩
lemma weight59_contains : weight59.Contains (fejerWeight 59) := by
  have he : weightBoxCalc 59 = weight59 := by decide +kernel
  rw [← he]
  exact weightBoxCalc_contains 59
def weight60 : RBox := ⟨4148387926380572560405783704,4148387926380572560444667908⟩
lemma weight60_contains : weight60.Contains (fejerWeight 60) := by
  have he : weightBoxCalc 60 = weight60 := by decide +kernel
  rw [← he]
  exact weightBoxCalc_contains 60
def weight61 : RBox := ⟨4203684105357756689347247211,4203684105357756689386809776⟩
lemma weight61_contains : weight61.Contains (fejerWeight 61) := by
  have he : weightBoxCalc 61 = weight61 := by decide +kernel
  rw [← he]
  exact weightBoxCalc_contains 61
def weight62 : RBox := ⟨4258093723759144794982340322,4258093723759144795022646015⟩
lemma weight62_contains : weight62.Contains (fejerWeight 62) := by
  have he : weightBoxCalc 62 = weight62 := by decide +kernel
  rw [← he]
  exact weightBoxCalc_contains 62
def weight63 : RBox := ⟨4312109436740432513532833577,4312109436740432513573832333⟩
lemma weight63_contains : weight63.Contains (fejerWeight 63) := by
  have he : weightBoxCalc 63 = weight63 := by decide +kernel
  rw [← he]
  exact weightBoxCalc_contains 63
def weight64 : RBox := ⟨4365234412735279897693917680,4365234412735279897730965810⟩
lemma weight64_contains : weight64.Contains (fejerWeight 64) := by
  have he : weightBoxCalc 64 = weight64 := by decide +kernel
  rw [← he]
  exact weightBoxCalc_contains 64
def weight65 : RBox := ⟨4417937498196211298645475243,4417937498196211298683967058⟩
lemma weight65_contains : weight65.Contains (fejerWeight 65) := by
  have he : weightBoxCalc 65 = weight65 := by decide +kernel
  rw [← he]
  exact weightBoxCalc_contains 65
def weight66 : RBox := ⟨4469745472103646047367985364,4469745472103646047407736227⟩
lemma weight66_contains : weight66.Contains (fejerWeight 66) := by
  have he : weightBoxCalc 66 = weight66 := by decide +kernel
  rw [← he]
  exact weightBoxCalc_contains 66
def weight67 : RBox := ⟨4521104527428516025268053090,4521104527428516025308869170⟩
lemma weight67_contains : weight67.Contains (fejerWeight 67) := by
  have he : weightBoxCalc 67 = weight67 := by decide +kernel
  rw [← he]
  exact weightBoxCalc_contains 67
def weight68 : RBox := ⟨4571563962896684265919348515,4571563962896684265961169848⟩
lemma weight68_contains : weight68.Contains (fejerWeight 68) := by
  have he : weightBoxCalc 68 = weight68 := by decide +kernel
  rw [← he]
  exact weightBoxCalc_contains 68
def weight69 : RBox := ⟨4621548366671504275910620453,4621548366671504275953595050⟩
lemma weight69_contains : weight69.Contains (fejerWeight 69) := by
  have he : weightBoxCalc 69 = weight69 := by decide +kernel
  rw [← he]
  exact weightBoxCalc_contains 69
def weight70 : RBox := ⟨4670628566542280100406672370,4670628566542280100450335668⟩
lemma weight70_contains : weight70.Contains (fejerWeight 70) := by
  have he : weightBoxCalc 70 = weight70 := by decide +kernel
  rw [← he]
  exact weightBoxCalc_contains 70
def weight71 : RBox := ⟨4719208499907091423913653871,4719208499907091423958310713⟩
lemma weight71_contains : weight71.Contains (fejerWeight 71) := by
  have he : weightBoxCalc 71 = weight71 := by decide +kernel
  rw [← he]
  exact weightBoxCalc_contains 71
def weight72 : RBox := ⟨4766879622005270934461156066,4766879622005270934506893110⟩
lemma weight72_contains : weight72.Contains (fejerWeight 72) := by
  have he : weightBoxCalc 72 = weight72 := by decide +kernel
  rw [← he]
  exact weightBoxCalc_contains 72
def weight73 : RBox := ⟨4814026089129177405541274014,4814026089129177405586692181⟩
lemma weight73_contains : weight73.Contains (fejerWeight 73) := by
  have he : weightBoxCalc 73 = weight73 := by decide +kernel
  rw [← he]
  exact weightBoxCalc_contains 73
def weight74 : RBox := ⟨4860259161897908846125205151,4860259161897908846171771874⟩
lemma weight74_contains : weight74.Contains (fejerWeight 74) := by
  have he : weightBoxCalc 74 = weight74 := by decide +kernel
  rw [← he]
  exact weightBoxCalc_contains 74
def weight75 : RBox := ⟨4905944009626571011820739023,4905944009626571011868183188⟩
lemma weight75_contains : weight75.Contains (fejerWeight 75) := by
  have he : weightBoxCalc 75 = weight75 := by decide +kernel
  rw [← he]
  exact weightBoxCalc_contains 75
def weight76 : RBox := ⟨4950710947543460949446198875,4950710947543460949494668528⟩
lemma weight76_contains : weight76.Contains (fejerWeight 76) := by
  have he : weightBoxCalc 76 = weight76 := by decide +kernel
  rw [← he]
  exact weightBoxCalc_contains 76
def weight77 : RBox := ⟨4994906884258064817896192089,4994906884258064817945143243⟩
lemma weight77_contains : weight77.Contains (fejerWeight 77) := by
  have he : weightBoxCalc 77 = weight77 := by decide +kernel
  rw [← he]
  exact weightBoxCalc_contains 77
def weight78 : RBox := ⟨5038180502976556968602523833,5038180502976556968652511470⟩
lemma weight78_contains : weight78.Contains (fejerWeight 78) := by
  have he : weightBoxCalc 78 = weight78 := by decide +kernel
  rw [← he]
  exact weightBoxCalc_contains 78
def weight79 : RBox := ⟨5080861116694780349872131194,5080861116694780349922812725⟩
lemma weight79_contains : weight79.Contains (fejerWeight 79) := by
  have he : weightBoxCalc 79 = weight79 := by decide +kernel
  rw [← he]
  exact weightBoxCalc_contains 79
def weight80 : RBox := ⟨5122615147863599496077058279,5122615147863599496128586170⟩
lemma weight80_contains : weight80.Contains (fejerWeight 80) := by
  have he : weightBoxCalc 80 = weight80 := by decide +kernel
  rw [← he]
  exact weightBoxCalc_contains 80
def weight81 : RBox := ⟨5163754923606351388193965764,5163754923606351388246311318⟩
lemma weight81_contains : weight81.Contains (fejerWeight 81) := by
  have he : weightBoxCalc 81 = weight81 := by decide +kernel
  rw [← he]
  exact weightBoxCalc_contains 81
def weight82 : RBox := ⟨5203964029326471386036971237,5203964029326471386090275722⟩
lemma weight82_contains : weight82.Contains (fejerWeight 82) := by
  have he : weightBoxCalc 82 = weight82 := by decide +kernel
  rw [← he]
  exact weightBoxCalc_contains 82
def weight83 : RBox := ⟨5243538365768798222281081767,5243538365768798222335283451⟩
lemma weight83_contains : weight83.Contains (fejerWeight 83) := by
  have he : weightBoxCalc 83 = weight83 := by decide +kernel
  rw [← he]
  exact weightBoxCalc_contains 83
def weight84 : RBox := ⟨5282178152652859128880119892,5282178152652859128935269874⟩
lemma weight84_contains : weight84.Contains (fejerWeight 84) := by
  have he : weightBoxCalc 84 = weight84 := by decide +kernel
  rw [← he]
  exact weightBoxCalc_contains 84
def weight85 : RBox := ⟨5320163378073107812640346059,5320163378073107812687155434⟩
lemma weight85_contains : weight85.Contains (fejerWeight 85) := by
  have he : weightBoxCalc 85 = weight85 := by decide +kernel
  rw [← he]
  exact weightBoxCalc_contains 85
def weight86 : RBox := ⟨5357210410876725006568461725,5357210410876725006616718030⟩
lemma weight86_contains : weight86.Contains (fejerWeight 86) := by
  have he : weightBoxCalc 86 = weight86 := by decide +kernel
  rw [← he]
  exact weightBoxCalc_contains 86
def weight87 : RBox := ⟨5393583798414604488183752538,5393583798414604488233198368⟩
lemma weight87_contains : weight87.Contains (fejerWeight 87) := by
  have he : weightBoxCalc 87 = weight87 := by decide +kernel
  rw [← he]
  exact weightBoxCalc_contains 87
def weight88 : RBox := ⟨5429015613212777300093035064,5429015613212777300143507747⟩
lemma weight88_contains : weight88.Contains (fejerWeight 88) := by
  have he : weightBoxCalc 88 = weight88 := by decide +kernel
  rw [← he]
  exact weightBoxCalc_contains 88
def weight89 : RBox := ⟨5463755395444195765818327306,5463755395444195765869783867⟩
lemma weight89_contains : weight89.Contains (fejerWeight 89) := by
  have he : weightBoxCalc 89 = weight89 := by decide +kernel
  rw [← he]
  exact weightBoxCalc_contains 89
def weight90 : RBox := ⟨5497550512329186233885497466,5497550512329186233937704682⟩
lemma weight90_contains : weight90.Contains (fejerWeight 90) := by
  have he : weightBoxCalc 90 = weight90 := by decide +kernel
  rw [← he]
  exact weightBoxCalc_contains 90
def weight91 : RBox := ⟨5530635895163525312794999161,5530635895163525312847895961⟩
lemma weight91_contains : weight91.Contains (fejerWeight 91) := by
  have he : weightBoxCalc 91 = weight91 := by decide +kernel
  rw [← he]
  exact weightBoxCalc_contains 91
def weight92 : RBox := ⟨5562773830443257907889391218,5562773830443257907943286989⟩
lemma weight92_contains : weight92.Contains (fejerWeight 92) := by
  have he : weightBoxCalc 92 = weight92 := by decide +kernel
  rw [← he]
  exact weightBoxCalc_contains 92
def weight93 : RBox := ⟨5594185006346973022951936561,5594185006346973023006345981⟩
lemma weight93_contains : weight93.Contains (fejerWeight 93) := by
  have he : weightBoxCalc 93 = weight93 := by decide +kernel
  rw [← he]
  exact weightBoxCalc_contains 93
def weight94 : RBox := ⟨5624646284225296969628806005,5624646284225296969684011897⟩
lemma weight94_contains : weight94.Contains (fejerWeight 94) := by
  have he : weightBoxCalc 94 = weight94 := by decide +kernel
  rw [← he]
  exact weightBoxCalc_contains 94
def weight95 : RBox := ⟨5654364444774320582459724612,5654364444774320582515799649⟩
lemma weight95_contains : weight95.Contains (fejerWeight 95) := by
  have he : weightBoxCalc 95 = weight95 := by decide +kernel
  rw [← he]
  exact weightBoxCalc_contains 95
def weight96 : RBox := ⟨5683130608496451681330841381,5683130608496451681386793267⟩
lemma weight96_contains : weight96.Contains (fejerWeight 96) := by
  have he : weightBoxCalc 96 = weight96 := by decide +kernel
  rw [← he]
  exact weightBoxCalc_contains 96
def weight97 : RBox := ⟨5711137956258757353545980461,5711137956258757353602979817⟩
lemma weight97_contains : weight97.Contains (fejerWeight 97) := by
  have he : weightBoxCalc 97 = weight97 := by decide +kernel
  rw [← he]
  exact weightBoxCalc_contains 97
def weight98 : RBox := ⟨5738191578706934836420499339,5738191578706934836477926701⟩
lemma weight98_contains : weight98.Contains (fejerWeight 98) := by
  have he : weightBoxCalc 98 = weight98 := by decide +kernel
  rw [← he]
  exact weightBoxCalc_contains 98
def weight99 : RBox := ⟨5764471338455741720009888145,5764471338455741720068327548⟩
lemma weight99_contains : weight99.Contains (fejerWeight 99) := by
  have he : weightBoxCalc 99 = weight99 := by decide +kernel
  rw [← he]
  exact weightBoxCalc_contains 99
def weight100 : RBox := ⟨5789796032181644714564789747,5789796032181644714623896598⟩
lemma weight100_contains : weight100.Contains (fejerWeight 100) := by
  have he : weightBoxCalc 100 = weight100 := by decide +kernel
  rw [← he]
  exact weightBoxCalc_contains 100
def weight101 : RBox := ⟨5814332461439061669678303244,5814332461439061669738242470⟩
lemma weight101_contains : weight101.Contains (fejerWeight 101) := by
  have he : weightBoxCalc 101 = weight101 := by decide +kernel
  rw [← he]
  exact weightBoxCalc_contains 101
def weight102 : RBox := ⟨5837912888120867156421880561,5837912888120867156479479947⟩
lemma weight102_contains : weight102.Contains (fejerWeight 102) := by
  have he : weightBoxCalc 102 = weight102 := by decide +kernel
  rw [← he]
  exact weightBoxCalc_contains 102
def weight103 : RBox := ⟨5860691287031258742944125056,5860691287031258743002818748⟩
lemma weight103_contains : weight103.Contains (fejerWeight 103) := by
  have he : weightBoxCalc 103 = weight103 := by decide +kernel
  rw [← he]
  exact weightBoxCalc_contains 103
def weight104 : RBox := ⟨5882513166344419020279517789,5882513166344419020338985693⟩
lemma weight104_contains : weight104.Contains (fejerWeight 104) := by
  have he : weightBoxCalc 104 = weight104 := by decide +kernel
  rw [← he]
  exact weightBoxCalc_contains 104
def weight105 : RBox := ⟨5903519886876394149683081285,5903519886876394149743135384⟩
lemma weight105_contains : weight105.Contains (fejerWeight 105) := by
  have he : weightBoxCalc 105 = weight105 := by decide +kernel
  rw [← he]
  exact weightBoxCalc_contains 105
def weight106 : RBox := ⟨5923570004768291589841432042,5923570004768291589902254387⟩
lemma weight106_contains : weight106.Contains (fejerWeight 106) := by
  have he : weightBoxCalc 106 = weight106 := by decide +kernel
  rw [← he]
  exact weightBoxCalc_contains 106
def weight107 : RBox := ⟨5942792459243946814942791692,5942792459243946815004006348⟩
lemma weight107_contains : weight107.Contains (fejerWeight 107) := by
  have he : weightBoxCalc 107 = weight107 := by decide +kernel
  rw [← he]
  exact weightBoxCalc_contains 107
def weight108 : RBox := ⟨5961058675603567321367733201,5961058675603567321429518010⟩
lemma weight108_contains : weight108.Contains (fejerWeight 108) := by
  have he : weightBoxCalc 108 = weight108 := by decide +kernel
  rw [← he]
  exact weightBoxCalc_contains 108
def weight109 : RBox := ⟨5978485344553441828649813117,5978485344553441828712371674⟩
lemma weight109_contains : weight109.Contains (fejerWeight 109) := by
  have he : weightBoxCalc 109 = weight109 := by decide +kernel
  rw [← he]
  exact weightBoxCalc_contains 109
def weight110 : RBox := ⟨5994956600268112465129793706,5994956600268112465191587026⟩
lemma weight110_contains : weight110.Contains (fejerWeight 110) := by
  have he : weightBoxCalc 110 = weight110 := by decide +kernel
  rw [← he]
  exact weightBoxCalc_contains 110
def weight111 : RBox := ⟨6010577039610215329321111218,6010577039610215329383501659⟩
lemma weight111_contains : weight111.Contains (fejerWeight 111) := by
  have he : weightBoxCalc 111 = weight111 := by decide +kernel
  rw [← he]
  exact weightBoxCalc_contains 111
def weight112 : RBox := ⟨6025243363002289724447107809,6025243363002289724509915577⟩
lemma weight112_contains : weight112.Contains (fejerWeight 112) := by
  have he : weightBoxCalc 112 = weight112 := by decide +kernel
  rw [← he]
  exact weightBoxCalc_contains 112
def weight113 : RBox := ⟨6039048210543529021123302047,6039048210543529021186703621⟩
lemma weight113_contains : weight113.Contains (fejerWeight 113) := by
  have he : weightBoxCalc 113 = weight113 := by decide +kernel
  rw [← he]
  exact weightBoxCalc_contains 113
def weight114 : RBox := ⟨6051900723180687647293955314,6051900723180687647357112135⟩
lemma weight114_contains : weight114.Contains (fejerWeight 114) := by
  have he : weightBoxCalc 114 = weight114 := by decide +kernel
  rw [← he]
  exact weightBoxCalc_contains 114
def weight115 : RBox := ⟨6063881704439054837188115369,6063881704439054837251687435⟩
lemma weight115_contains : weight115.Contains (fejerWeight 115) := by
  have he : weightBoxCalc 115 = weight115 := by decide +kernel
  rw [← he]
  exact weightBoxCalc_contains 115
def weight116 : RBox := ⟨6074912626312625515276774213,6074912626312625515340247587⟩
lemma weight116_contains : weight116.Contains (fejerWeight 116) := by
  have he : weightBoxCalc 116 = weight116 := by decide +kernel
  rw [← he]
  exact weightBoxCalc_contains 116
def weight117 : RBox := ⟨6085062559658558052385052499,6085062559658558052448978448⟩
lemma weight117_contains : weight117.Contains (fejerWeight 117) := by
  have he : weightBoxCalc 117 = weight117 := by decide +kernel
  rw [← he]
  exact weightBoxCalc_contains 117
def weight118 : RBox := ⟨6094265213724962908278863582,6094265213724962908342833342⟩
lemma weight118_contains : weight118.Contains (fejerWeight 118) := by
  have he : weightBoxCalc 118 = weight118 := by decide +kernel
  rw [← he]
  exact weightBoxCalc_contains 118
def weight119 : RBox := ⟨6102578014840415589665675058,6102578014840415589729688779⟩
lemma weight119_contains : weight119.Contains (fejerWeight 119) := by
  have he : weightBoxCalc 119 = weight119 := by decide +kernel
  rw [← he]
  exact weightBoxCalc_contains 119
def weight120 : RBox := ⟨6109946830921520823412964797,6109946830921520823477045083⟩
lemma weight120_contains : weight120.Contains (fejerWeight 120) := by
  have he : weightBoxCalc 120 = weight120 := by decide +kernel
  rw [← he]
  exact weightBoxCalc_contains 120
def weight121 : RBox := ⟨6116417516575415400105359979,6116417516575415400169578642⟩
lemma weight121_contains : weight121.Contains (fejerWeight 121) := by
  have he : weightBoxCalc 121 = weight121 := by decide +kernel
  rw [← he]
  exact weightBoxCalc_contains 121
def weight122 : RBox := ⟨6121948034614205269491689602,6121948034614205269555839779⟩
lemma weight122_contains : weight122.Contains (fejerWeight 122) := by
  have he : weightBoxCalc 122 = weight122 := by decide +kernel
  rw [← he]
  exact weightBoxCalc_contains 122
def weight123 : RBox := ⟨6126572725753092566573313075,6126572725753092566637440834⟩
lemma weight123_contains : weight123.Contains (fejerWeight 123) := by
  have he : weightBoxCalc 123 = weight123 := by decide +kernel
  rw [← he]
  exact weightBoxCalc_contains 123
def weight124 : RBox := ⟨6130261598421713790436417950,6130261598421713790500332217⟩
lemma weight124_contains : weight124.Contains (fejerWeight 124) := by
  have he : weightBoxCalc 124 = weight124 := by decide +kernel
  rw [← he]
  exact weightBoxCalc_contains 124
def weight125 : RBox := ⟨6133037522574668035260086108,6133037522574668035323722931⟩
lemma weight125_contains : weight125.Contains (fejerWeight 125) := by
  have he : weightBoxCalc 125 = weight125 := by decide +kernel
  rw [← he]
  exact weightBoxCalc_contains 125
def weight126 : RBox := ⟨6134882517232499617024723204,6134882517232499617087919323⟩
lemma weight126_contains : weight126.Contains (fejerWeight 126) := by
  have he : weightBoxCalc 126 = weight126 := by decide +kernel
  rw [← he]
  exact weightBoxCalc_contains 126
def weight127 : RBox := ⟨6135808010229466395145471605,6135808010229466395208006666⟩
lemma weight127_contains : weight127.Contains (fejerWeight 127) := by
  have he : weightBoxCalc 127 = weight127 := by decide +kernel
  rw [← he]
  exact weightBoxCalc_contains 127
def weight128 : RBox := weight127
lemma weight128_contains : weight128.Contains (fejerWeight 128) := by
  rw [← fejerWeight_reverse 128 (by decide)]
  exact weight127_contains
def weight129 : RBox := weight126
lemma weight129_contains : weight129.Contains (fejerWeight 129) := by
  rw [← fejerWeight_reverse 129 (by decide)]
  exact weight126_contains
def weight130 : RBox := weight125
lemma weight130_contains : weight130.Contains (fejerWeight 130) := by
  rw [← fejerWeight_reverse 130 (by decide)]
  exact weight125_contains
def weight131 : RBox := weight124
lemma weight131_contains : weight131.Contains (fejerWeight 131) := by
  rw [← fejerWeight_reverse 131 (by decide)]
  exact weight124_contains
def weight132 : RBox := weight123
lemma weight132_contains : weight132.Contains (fejerWeight 132) := by
  rw [← fejerWeight_reverse 132 (by decide)]
  exact weight123_contains
def weight133 : RBox := weight122
lemma weight133_contains : weight133.Contains (fejerWeight 133) := by
  rw [← fejerWeight_reverse 133 (by decide)]
  exact weight122_contains
def weight134 : RBox := weight121
lemma weight134_contains : weight134.Contains (fejerWeight 134) := by
  rw [← fejerWeight_reverse 134 (by decide)]
  exact weight121_contains
def weight135 : RBox := weight120
lemma weight135_contains : weight135.Contains (fejerWeight 135) := by
  rw [← fejerWeight_reverse 135 (by decide)]
  exact weight120_contains
def weight136 : RBox := weight119
lemma weight136_contains : weight136.Contains (fejerWeight 136) := by
  rw [← fejerWeight_reverse 136 (by decide)]
  exact weight119_contains
def weight137 : RBox := weight118
lemma weight137_contains : weight137.Contains (fejerWeight 137) := by
  rw [← fejerWeight_reverse 137 (by decide)]
  exact weight118_contains
def weight138 : RBox := weight117
lemma weight138_contains : weight138.Contains (fejerWeight 138) := by
  rw [← fejerWeight_reverse 138 (by decide)]
  exact weight117_contains
def weight139 : RBox := weight116
lemma weight139_contains : weight139.Contains (fejerWeight 139) := by
  rw [← fejerWeight_reverse 139 (by decide)]
  exact weight116_contains
def weight140 : RBox := weight115
lemma weight140_contains : weight140.Contains (fejerWeight 140) := by
  rw [← fejerWeight_reverse 140 (by decide)]
  exact weight115_contains
def weight141 : RBox := weight114
lemma weight141_contains : weight141.Contains (fejerWeight 141) := by
  rw [← fejerWeight_reverse 141 (by decide)]
  exact weight114_contains
def weight142 : RBox := weight113
lemma weight142_contains : weight142.Contains (fejerWeight 142) := by
  rw [← fejerWeight_reverse 142 (by decide)]
  exact weight113_contains
def weight143 : RBox := weight112
lemma weight143_contains : weight143.Contains (fejerWeight 143) := by
  rw [← fejerWeight_reverse 143 (by decide)]
  exact weight112_contains
def weight144 : RBox := weight111
lemma weight144_contains : weight144.Contains (fejerWeight 144) := by
  rw [← fejerWeight_reverse 144 (by decide)]
  exact weight111_contains
def weight145 : RBox := weight110
lemma weight145_contains : weight145.Contains (fejerWeight 145) := by
  rw [← fejerWeight_reverse 145 (by decide)]
  exact weight110_contains
def weight146 : RBox := weight109
lemma weight146_contains : weight146.Contains (fejerWeight 146) := by
  rw [← fejerWeight_reverse 146 (by decide)]
  exact weight109_contains
def weight147 : RBox := weight108
lemma weight147_contains : weight147.Contains (fejerWeight 147) := by
  rw [← fejerWeight_reverse 147 (by decide)]
  exact weight108_contains
def weight148 : RBox := weight107
lemma weight148_contains : weight148.Contains (fejerWeight 148) := by
  rw [← fejerWeight_reverse 148 (by decide)]
  exact weight107_contains
def weight149 : RBox := weight106
lemma weight149_contains : weight149.Contains (fejerWeight 149) := by
  rw [← fejerWeight_reverse 149 (by decide)]
  exact weight106_contains
def weight150 : RBox := weight105
lemma weight150_contains : weight150.Contains (fejerWeight 150) := by
  rw [← fejerWeight_reverse 150 (by decide)]
  exact weight105_contains
def weight151 : RBox := weight104
lemma weight151_contains : weight151.Contains (fejerWeight 151) := by
  rw [← fejerWeight_reverse 151 (by decide)]
  exact weight104_contains
def weight152 : RBox := weight103
lemma weight152_contains : weight152.Contains (fejerWeight 152) := by
  rw [← fejerWeight_reverse 152 (by decide)]
  exact weight103_contains
def weight153 : RBox := weight102
lemma weight153_contains : weight153.Contains (fejerWeight 153) := by
  rw [← fejerWeight_reverse 153 (by decide)]
  exact weight102_contains
def weight154 : RBox := weight101
lemma weight154_contains : weight154.Contains (fejerWeight 154) := by
  rw [← fejerWeight_reverse 154 (by decide)]
  exact weight101_contains
def weight155 : RBox := weight100
lemma weight155_contains : weight155.Contains (fejerWeight 155) := by
  rw [← fejerWeight_reverse 155 (by decide)]
  exact weight100_contains
def weight156 : RBox := weight99
lemma weight156_contains : weight156.Contains (fejerWeight 156) := by
  rw [← fejerWeight_reverse 156 (by decide)]
  exact weight99_contains
def weight157 : RBox := weight98
lemma weight157_contains : weight157.Contains (fejerWeight 157) := by
  rw [← fejerWeight_reverse 157 (by decide)]
  exact weight98_contains
def weight158 : RBox := weight97
lemma weight158_contains : weight158.Contains (fejerWeight 158) := by
  rw [← fejerWeight_reverse 158 (by decide)]
  exact weight97_contains
def weight159 : RBox := weight96
lemma weight159_contains : weight159.Contains (fejerWeight 159) := by
  rw [← fejerWeight_reverse 159 (by decide)]
  exact weight96_contains
def weight160 : RBox := weight95
lemma weight160_contains : weight160.Contains (fejerWeight 160) := by
  rw [← fejerWeight_reverse 160 (by decide)]
  exact weight95_contains
def weight161 : RBox := weight94
lemma weight161_contains : weight161.Contains (fejerWeight 161) := by
  rw [← fejerWeight_reverse 161 (by decide)]
  exact weight94_contains
def weight162 : RBox := weight93
lemma weight162_contains : weight162.Contains (fejerWeight 162) := by
  rw [← fejerWeight_reverse 162 (by decide)]
  exact weight93_contains
def weight163 : RBox := weight92
lemma weight163_contains : weight163.Contains (fejerWeight 163) := by
  rw [← fejerWeight_reverse 163 (by decide)]
  exact weight92_contains
def weight164 : RBox := weight91
lemma weight164_contains : weight164.Contains (fejerWeight 164) := by
  rw [← fejerWeight_reverse 164 (by decide)]
  exact weight91_contains
def weight165 : RBox := weight90
lemma weight165_contains : weight165.Contains (fejerWeight 165) := by
  rw [← fejerWeight_reverse 165 (by decide)]
  exact weight90_contains
def weight166 : RBox := weight89
lemma weight166_contains : weight166.Contains (fejerWeight 166) := by
  rw [← fejerWeight_reverse 166 (by decide)]
  exact weight89_contains
def weight167 : RBox := weight88
lemma weight167_contains : weight167.Contains (fejerWeight 167) := by
  rw [← fejerWeight_reverse 167 (by decide)]
  exact weight88_contains
def weight168 : RBox := weight87
lemma weight168_contains : weight168.Contains (fejerWeight 168) := by
  rw [← fejerWeight_reverse 168 (by decide)]
  exact weight87_contains
def weight169 : RBox := weight86
lemma weight169_contains : weight169.Contains (fejerWeight 169) := by
  rw [← fejerWeight_reverse 169 (by decide)]
  exact weight86_contains
def weight170 : RBox := weight85
lemma weight170_contains : weight170.Contains (fejerWeight 170) := by
  rw [← fejerWeight_reverse 170 (by decide)]
  exact weight85_contains
def weight171 : RBox := weight84
lemma weight171_contains : weight171.Contains (fejerWeight 171) := by
  rw [← fejerWeight_reverse 171 (by decide)]
  exact weight84_contains
def weight172 : RBox := weight83
lemma weight172_contains : weight172.Contains (fejerWeight 172) := by
  rw [← fejerWeight_reverse 172 (by decide)]
  exact weight83_contains
def weight173 : RBox := weight82
lemma weight173_contains : weight173.Contains (fejerWeight 173) := by
  rw [← fejerWeight_reverse 173 (by decide)]
  exact weight82_contains
def weight174 : RBox := weight81
lemma weight174_contains : weight174.Contains (fejerWeight 174) := by
  rw [← fejerWeight_reverse 174 (by decide)]
  exact weight81_contains
def weight175 : RBox := weight80
lemma weight175_contains : weight175.Contains (fejerWeight 175) := by
  rw [← fejerWeight_reverse 175 (by decide)]
  exact weight80_contains
def weight176 : RBox := weight79
lemma weight176_contains : weight176.Contains (fejerWeight 176) := by
  rw [← fejerWeight_reverse 176 (by decide)]
  exact weight79_contains
def weight177 : RBox := weight78
lemma weight177_contains : weight177.Contains (fejerWeight 177) := by
  rw [← fejerWeight_reverse 177 (by decide)]
  exact weight78_contains
def weight178 : RBox := weight77
lemma weight178_contains : weight178.Contains (fejerWeight 178) := by
  rw [← fejerWeight_reverse 178 (by decide)]
  exact weight77_contains
def weight179 : RBox := weight76
lemma weight179_contains : weight179.Contains (fejerWeight 179) := by
  rw [← fejerWeight_reverse 179 (by decide)]
  exact weight76_contains
def weight180 : RBox := weight75
lemma weight180_contains : weight180.Contains (fejerWeight 180) := by
  rw [← fejerWeight_reverse 180 (by decide)]
  exact weight75_contains
def weight181 : RBox := weight74
lemma weight181_contains : weight181.Contains (fejerWeight 181) := by
  rw [← fejerWeight_reverse 181 (by decide)]
  exact weight74_contains
def weight182 : RBox := weight73
lemma weight182_contains : weight182.Contains (fejerWeight 182) := by
  rw [← fejerWeight_reverse 182 (by decide)]
  exact weight73_contains
def weight183 : RBox := weight72
lemma weight183_contains : weight183.Contains (fejerWeight 183) := by
  rw [← fejerWeight_reverse 183 (by decide)]
  exact weight72_contains
def weight184 : RBox := weight71
lemma weight184_contains : weight184.Contains (fejerWeight 184) := by
  rw [← fejerWeight_reverse 184 (by decide)]
  exact weight71_contains
def weight185 : RBox := weight70
lemma weight185_contains : weight185.Contains (fejerWeight 185) := by
  rw [← fejerWeight_reverse 185 (by decide)]
  exact weight70_contains
def weight186 : RBox := weight69
lemma weight186_contains : weight186.Contains (fejerWeight 186) := by
  rw [← fejerWeight_reverse 186 (by decide)]
  exact weight69_contains
def weight187 : RBox := weight68
lemma weight187_contains : weight187.Contains (fejerWeight 187) := by
  rw [← fejerWeight_reverse 187 (by decide)]
  exact weight68_contains
def weight188 : RBox := weight67
lemma weight188_contains : weight188.Contains (fejerWeight 188) := by
  rw [← fejerWeight_reverse 188 (by decide)]
  exact weight67_contains
def weight189 : RBox := weight66
lemma weight189_contains : weight189.Contains (fejerWeight 189) := by
  rw [← fejerWeight_reverse 189 (by decide)]
  exact weight66_contains
def weight190 : RBox := weight65
lemma weight190_contains : weight190.Contains (fejerWeight 190) := by
  rw [← fejerWeight_reverse 190 (by decide)]
  exact weight65_contains
def weight191 : RBox := weight64
lemma weight191_contains : weight191.Contains (fejerWeight 191) := by
  rw [← fejerWeight_reverse 191 (by decide)]
  exact weight64_contains
def weight192 : RBox := weight63
lemma weight192_contains : weight192.Contains (fejerWeight 192) := by
  rw [← fejerWeight_reverse 192 (by decide)]
  exact weight63_contains
def weight193 : RBox := weight62
lemma weight193_contains : weight193.Contains (fejerWeight 193) := by
  rw [← fejerWeight_reverse 193 (by decide)]
  exact weight62_contains
def weight194 : RBox := weight61
lemma weight194_contains : weight194.Contains (fejerWeight 194) := by
  rw [← fejerWeight_reverse 194 (by decide)]
  exact weight61_contains
def weight195 : RBox := weight60
lemma weight195_contains : weight195.Contains (fejerWeight 195) := by
  rw [← fejerWeight_reverse 195 (by decide)]
  exact weight60_contains
def weight196 : RBox := weight59
lemma weight196_contains : weight196.Contains (fejerWeight 196) := by
  rw [← fejerWeight_reverse 196 (by decide)]
  exact weight59_contains
def weight197 : RBox := weight58
lemma weight197_contains : weight197.Contains (fejerWeight 197) := by
  rw [← fejerWeight_reverse 197 (by decide)]
  exact weight58_contains
def weight198 : RBox := weight57
lemma weight198_contains : weight198.Contains (fejerWeight 198) := by
  rw [← fejerWeight_reverse 198 (by decide)]
  exact weight57_contains
def weight199 : RBox := weight56
lemma weight199_contains : weight199.Contains (fejerWeight 199) := by
  rw [← fejerWeight_reverse 199 (by decide)]
  exact weight56_contains
def weight200 : RBox := weight55
lemma weight200_contains : weight200.Contains (fejerWeight 200) := by
  rw [← fejerWeight_reverse 200 (by decide)]
  exact weight55_contains
def weight201 : RBox := weight54
lemma weight201_contains : weight201.Contains (fejerWeight 201) := by
  rw [← fejerWeight_reverse 201 (by decide)]
  exact weight54_contains
def weight202 : RBox := weight53
lemma weight202_contains : weight202.Contains (fejerWeight 202) := by
  rw [← fejerWeight_reverse 202 (by decide)]
  exact weight53_contains
def weight203 : RBox := weight52
lemma weight203_contains : weight203.Contains (fejerWeight 203) := by
  rw [← fejerWeight_reverse 203 (by decide)]
  exact weight52_contains
def weight204 : RBox := weight51
lemma weight204_contains : weight204.Contains (fejerWeight 204) := by
  rw [← fejerWeight_reverse 204 (by decide)]
  exact weight51_contains
def weight205 : RBox := weight50
lemma weight205_contains : weight205.Contains (fejerWeight 205) := by
  rw [← fejerWeight_reverse 205 (by decide)]
  exact weight50_contains
def weight206 : RBox := weight49
lemma weight206_contains : weight206.Contains (fejerWeight 206) := by
  rw [← fejerWeight_reverse 206 (by decide)]
  exact weight49_contains
def weight207 : RBox := weight48
lemma weight207_contains : weight207.Contains (fejerWeight 207) := by
  rw [← fejerWeight_reverse 207 (by decide)]
  exact weight48_contains
def weight208 : RBox := weight47
lemma weight208_contains : weight208.Contains (fejerWeight 208) := by
  rw [← fejerWeight_reverse 208 (by decide)]
  exact weight47_contains
def weight209 : RBox := weight46
lemma weight209_contains : weight209.Contains (fejerWeight 209) := by
  rw [← fejerWeight_reverse 209 (by decide)]
  exact weight46_contains
def weight210 : RBox := weight45
lemma weight210_contains : weight210.Contains (fejerWeight 210) := by
  rw [← fejerWeight_reverse 210 (by decide)]
  exact weight45_contains
def weight211 : RBox := weight44
lemma weight211_contains : weight211.Contains (fejerWeight 211) := by
  rw [← fejerWeight_reverse 211 (by decide)]
  exact weight44_contains
def weight212 : RBox := weight43
lemma weight212_contains : weight212.Contains (fejerWeight 212) := by
  rw [← fejerWeight_reverse 212 (by decide)]
  exact weight43_contains
def weight213 : RBox := weight42
lemma weight213_contains : weight213.Contains (fejerWeight 213) := by
  rw [← fejerWeight_reverse 213 (by decide)]
  exact weight42_contains
def weight214 : RBox := weight41
lemma weight214_contains : weight214.Contains (fejerWeight 214) := by
  rw [← fejerWeight_reverse 214 (by decide)]
  exact weight41_contains
def weight215 : RBox := weight40
lemma weight215_contains : weight215.Contains (fejerWeight 215) := by
  rw [← fejerWeight_reverse 215 (by decide)]
  exact weight40_contains
def weight216 : RBox := weight39
lemma weight216_contains : weight216.Contains (fejerWeight 216) := by
  rw [← fejerWeight_reverse 216 (by decide)]
  exact weight39_contains
def weight217 : RBox := weight38
lemma weight217_contains : weight217.Contains (fejerWeight 217) := by
  rw [← fejerWeight_reverse 217 (by decide)]
  exact weight38_contains
def weight218 : RBox := weight37
lemma weight218_contains : weight218.Contains (fejerWeight 218) := by
  rw [← fejerWeight_reverse 218 (by decide)]
  exact weight37_contains
def weight219 : RBox := weight36
lemma weight219_contains : weight219.Contains (fejerWeight 219) := by
  rw [← fejerWeight_reverse 219 (by decide)]
  exact weight36_contains
def weight220 : RBox := weight35
lemma weight220_contains : weight220.Contains (fejerWeight 220) := by
  rw [← fejerWeight_reverse 220 (by decide)]
  exact weight35_contains
def weight221 : RBox := weight34
lemma weight221_contains : weight221.Contains (fejerWeight 221) := by
  rw [← fejerWeight_reverse 221 (by decide)]
  exact weight34_contains
def weight222 : RBox := weight33
lemma weight222_contains : weight222.Contains (fejerWeight 222) := by
  rw [← fejerWeight_reverse 222 (by decide)]
  exact weight33_contains
def weight223 : RBox := weight32
lemma weight223_contains : weight223.Contains (fejerWeight 223) := by
  rw [← fejerWeight_reverse 223 (by decide)]
  exact weight32_contains
def weight224 : RBox := weight31
lemma weight224_contains : weight224.Contains (fejerWeight 224) := by
  rw [← fejerWeight_reverse 224 (by decide)]
  exact weight31_contains
def weight225 : RBox := weight30
lemma weight225_contains : weight225.Contains (fejerWeight 225) := by
  rw [← fejerWeight_reverse 225 (by decide)]
  exact weight30_contains
def weight226 : RBox := weight29
lemma weight226_contains : weight226.Contains (fejerWeight 226) := by
  rw [← fejerWeight_reverse 226 (by decide)]
  exact weight29_contains
def weight227 : RBox := weight28
lemma weight227_contains : weight227.Contains (fejerWeight 227) := by
  rw [← fejerWeight_reverse 227 (by decide)]
  exact weight28_contains
def weight228 : RBox := weight27
lemma weight228_contains : weight228.Contains (fejerWeight 228) := by
  rw [← fejerWeight_reverse 228 (by decide)]
  exact weight27_contains
def weight229 : RBox := weight26
lemma weight229_contains : weight229.Contains (fejerWeight 229) := by
  rw [← fejerWeight_reverse 229 (by decide)]
  exact weight26_contains
def weight230 : RBox := weight25
lemma weight230_contains : weight230.Contains (fejerWeight 230) := by
  rw [← fejerWeight_reverse 230 (by decide)]
  exact weight25_contains
def weight231 : RBox := weight24
lemma weight231_contains : weight231.Contains (fejerWeight 231) := by
  rw [← fejerWeight_reverse 231 (by decide)]
  exact weight24_contains
def weight232 : RBox := weight23
lemma weight232_contains : weight232.Contains (fejerWeight 232) := by
  rw [← fejerWeight_reverse 232 (by decide)]
  exact weight23_contains
def weight233 : RBox := weight22
lemma weight233_contains : weight233.Contains (fejerWeight 233) := by
  rw [← fejerWeight_reverse 233 (by decide)]
  exact weight22_contains
def weight234 : RBox := weight21
lemma weight234_contains : weight234.Contains (fejerWeight 234) := by
  rw [← fejerWeight_reverse 234 (by decide)]
  exact weight21_contains
def weight235 : RBox := weight20
lemma weight235_contains : weight235.Contains (fejerWeight 235) := by
  rw [← fejerWeight_reverse 235 (by decide)]
  exact weight20_contains
def weight236 : RBox := weight19
lemma weight236_contains : weight236.Contains (fejerWeight 236) := by
  rw [← fejerWeight_reverse 236 (by decide)]
  exact weight19_contains
def weight237 : RBox := weight18
lemma weight237_contains : weight237.Contains (fejerWeight 237) := by
  rw [← fejerWeight_reverse 237 (by decide)]
  exact weight18_contains
def weight238 : RBox := weight17
lemma weight238_contains : weight238.Contains (fejerWeight 238) := by
  rw [← fejerWeight_reverse 238 (by decide)]
  exact weight17_contains
def weight239 : RBox := weight16
lemma weight239_contains : weight239.Contains (fejerWeight 239) := by
  rw [← fejerWeight_reverse 239 (by decide)]
  exact weight16_contains
def weight240 : RBox := weight15
lemma weight240_contains : weight240.Contains (fejerWeight 240) := by
  rw [← fejerWeight_reverse 240 (by decide)]
  exact weight15_contains
def weight241 : RBox := weight14
lemma weight241_contains : weight241.Contains (fejerWeight 241) := by
  rw [← fejerWeight_reverse 241 (by decide)]
  exact weight14_contains
def weight242 : RBox := weight13
lemma weight242_contains : weight242.Contains (fejerWeight 242) := by
  rw [← fejerWeight_reverse 242 (by decide)]
  exact weight13_contains
def weight243 : RBox := weight12
lemma weight243_contains : weight243.Contains (fejerWeight 243) := by
  rw [← fejerWeight_reverse 243 (by decide)]
  exact weight12_contains
def weight244 : RBox := weight11
lemma weight244_contains : weight244.Contains (fejerWeight 244) := by
  rw [← fejerWeight_reverse 244 (by decide)]
  exact weight11_contains
def weight245 : RBox := weight10
lemma weight245_contains : weight245.Contains (fejerWeight 245) := by
  rw [← fejerWeight_reverse 245 (by decide)]
  exact weight10_contains
def weight246 : RBox := weight9
lemma weight246_contains : weight246.Contains (fejerWeight 246) := by
  rw [← fejerWeight_reverse 246 (by decide)]
  exact weight9_contains
def weight247 : RBox := weight8
lemma weight247_contains : weight247.Contains (fejerWeight 247) := by
  rw [← fejerWeight_reverse 247 (by decide)]
  exact weight8_contains
def weight248 : RBox := weight7
lemma weight248_contains : weight248.Contains (fejerWeight 248) := by
  rw [← fejerWeight_reverse 248 (by decide)]
  exact weight7_contains
def weight249 : RBox := weight6
lemma weight249_contains : weight249.Contains (fejerWeight 249) := by
  rw [← fejerWeight_reverse 249 (by decide)]
  exact weight6_contains
def weight250 : RBox := weight5
lemma weight250_contains : weight250.Contains (fejerWeight 250) := by
  rw [← fejerWeight_reverse 250 (by decide)]
  exact weight5_contains
def weight251 : RBox := weight4
lemma weight251_contains : weight251.Contains (fejerWeight 251) := by
  rw [← fejerWeight_reverse 251 (by decide)]
  exact weight4_contains
def weight252 : RBox := weight3
lemma weight252_contains : weight252.Contains (fejerWeight 252) := by
  rw [← fejerWeight_reverse 252 (by decide)]
  exact weight3_contains
def weight253 : RBox := weight2
lemma weight253_contains : weight253.Contains (fejerWeight 253) := by
  rw [← fejerWeight_reverse 253 (by decide)]
  exact weight2_contains
def weight254 : RBox := weight1
lemma weight254_contains : weight254.Contains (fejerWeight 254) := by
  rw [← fejerWeight_reverse 254 (by decide)]
  exact weight1_contains
def weight255 : RBox := weight0
lemma weight255_contains : weight255.Contains (fejerWeight 255) := by
  rw [← fejerWeight_reverse 255 (by decide)]
  exact weight0_contains
def weights0 : Fin 16 → RBox := ![weight0,weight1,weight2,weight3,weight4,weight5,weight6,weight7,weight8,weight9,weight10,weight11,weight12,weight13,weight14,weight15]
lemma weights0_contains (j : Fin 16) : (weights0 j).Contains (fejerWeight (0+j.val)) := by
  fin_cases j
  · exact weight0_contains
  · exact weight1_contains
  · exact weight2_contains
  · exact weight3_contains
  · exact weight4_contains
  · exact weight5_contains
  · exact weight6_contains
  · exact weight7_contains
  · exact weight8_contains
  · exact weight9_contains
  · exact weight10_contains
  · exact weight11_contains
  · exact weight12_contains
  · exact weight13_contains
  · exact weight14_contains
  · exact weight15_contains
def weights1 : Fin 16 → RBox := ![weight16,weight17,weight18,weight19,weight20,weight21,weight22,weight23,weight24,weight25,weight26,weight27,weight28,weight29,weight30,weight31]
lemma weights1_contains (j : Fin 16) : (weights1 j).Contains (fejerWeight (16+j.val)) := by
  fin_cases j
  · exact weight16_contains
  · exact weight17_contains
  · exact weight18_contains
  · exact weight19_contains
  · exact weight20_contains
  · exact weight21_contains
  · exact weight22_contains
  · exact weight23_contains
  · exact weight24_contains
  · exact weight25_contains
  · exact weight26_contains
  · exact weight27_contains
  · exact weight28_contains
  · exact weight29_contains
  · exact weight30_contains
  · exact weight31_contains
def weights2 : Fin 16 → RBox := ![weight32,weight33,weight34,weight35,weight36,weight37,weight38,weight39,weight40,weight41,weight42,weight43,weight44,weight45,weight46,weight47]
lemma weights2_contains (j : Fin 16) : (weights2 j).Contains (fejerWeight (32+j.val)) := by
  fin_cases j
  · exact weight32_contains
  · exact weight33_contains
  · exact weight34_contains
  · exact weight35_contains
  · exact weight36_contains
  · exact weight37_contains
  · exact weight38_contains
  · exact weight39_contains
  · exact weight40_contains
  · exact weight41_contains
  · exact weight42_contains
  · exact weight43_contains
  · exact weight44_contains
  · exact weight45_contains
  · exact weight46_contains
  · exact weight47_contains
def weights3 : Fin 16 → RBox := ![weight48,weight49,weight50,weight51,weight52,weight53,weight54,weight55,weight56,weight57,weight58,weight59,weight60,weight61,weight62,weight63]
lemma weights3_contains (j : Fin 16) : (weights3 j).Contains (fejerWeight (48+j.val)) := by
  fin_cases j
  · exact weight48_contains
  · exact weight49_contains
  · exact weight50_contains
  · exact weight51_contains
  · exact weight52_contains
  · exact weight53_contains
  · exact weight54_contains
  · exact weight55_contains
  · exact weight56_contains
  · exact weight57_contains
  · exact weight58_contains
  · exact weight59_contains
  · exact weight60_contains
  · exact weight61_contains
  · exact weight62_contains
  · exact weight63_contains
def weights4 : Fin 16 → RBox := ![weight64,weight65,weight66,weight67,weight68,weight69,weight70,weight71,weight72,weight73,weight74,weight75,weight76,weight77,weight78,weight79]
lemma weights4_contains (j : Fin 16) : (weights4 j).Contains (fejerWeight (64+j.val)) := by
  fin_cases j
  · exact weight64_contains
  · exact weight65_contains
  · exact weight66_contains
  · exact weight67_contains
  · exact weight68_contains
  · exact weight69_contains
  · exact weight70_contains
  · exact weight71_contains
  · exact weight72_contains
  · exact weight73_contains
  · exact weight74_contains
  · exact weight75_contains
  · exact weight76_contains
  · exact weight77_contains
  · exact weight78_contains
  · exact weight79_contains
def weights5 : Fin 16 → RBox := ![weight80,weight81,weight82,weight83,weight84,weight85,weight86,weight87,weight88,weight89,weight90,weight91,weight92,weight93,weight94,weight95]
lemma weights5_contains (j : Fin 16) : (weights5 j).Contains (fejerWeight (80+j.val)) := by
  fin_cases j
  · exact weight80_contains
  · exact weight81_contains
  · exact weight82_contains
  · exact weight83_contains
  · exact weight84_contains
  · exact weight85_contains
  · exact weight86_contains
  · exact weight87_contains
  · exact weight88_contains
  · exact weight89_contains
  · exact weight90_contains
  · exact weight91_contains
  · exact weight92_contains
  · exact weight93_contains
  · exact weight94_contains
  · exact weight95_contains
def weights6 : Fin 16 → RBox := ![weight96,weight97,weight98,weight99,weight100,weight101,weight102,weight103,weight104,weight105,weight106,weight107,weight108,weight109,weight110,weight111]
lemma weights6_contains (j : Fin 16) : (weights6 j).Contains (fejerWeight (96+j.val)) := by
  fin_cases j
  · exact weight96_contains
  · exact weight97_contains
  · exact weight98_contains
  · exact weight99_contains
  · exact weight100_contains
  · exact weight101_contains
  · exact weight102_contains
  · exact weight103_contains
  · exact weight104_contains
  · exact weight105_contains
  · exact weight106_contains
  · exact weight107_contains
  · exact weight108_contains
  · exact weight109_contains
  · exact weight110_contains
  · exact weight111_contains
def weights7 : Fin 16 → RBox := ![weight112,weight113,weight114,weight115,weight116,weight117,weight118,weight119,weight120,weight121,weight122,weight123,weight124,weight125,weight126,weight127]
lemma weights7_contains (j : Fin 16) : (weights7 j).Contains (fejerWeight (112+j.val)) := by
  fin_cases j
  · exact weight112_contains
  · exact weight113_contains
  · exact weight114_contains
  · exact weight115_contains
  · exact weight116_contains
  · exact weight117_contains
  · exact weight118_contains
  · exact weight119_contains
  · exact weight120_contains
  · exact weight121_contains
  · exact weight122_contains
  · exact weight123_contains
  · exact weight124_contains
  · exact weight125_contains
  · exact weight126_contains
  · exact weight127_contains
def weights8 : Fin 16 → RBox := ![weight128,weight129,weight130,weight131,weight132,weight133,weight134,weight135,weight136,weight137,weight138,weight139,weight140,weight141,weight142,weight143]
lemma weights8_contains (j : Fin 16) : (weights8 j).Contains (fejerWeight (128+j.val)) := by
  fin_cases j
  · exact weight128_contains
  · exact weight129_contains
  · exact weight130_contains
  · exact weight131_contains
  · exact weight132_contains
  · exact weight133_contains
  · exact weight134_contains
  · exact weight135_contains
  · exact weight136_contains
  · exact weight137_contains
  · exact weight138_contains
  · exact weight139_contains
  · exact weight140_contains
  · exact weight141_contains
  · exact weight142_contains
  · exact weight143_contains
def weights9 : Fin 16 → RBox := ![weight144,weight145,weight146,weight147,weight148,weight149,weight150,weight151,weight152,weight153,weight154,weight155,weight156,weight157,weight158,weight159]
lemma weights9_contains (j : Fin 16) : (weights9 j).Contains (fejerWeight (144+j.val)) := by
  fin_cases j
  · exact weight144_contains
  · exact weight145_contains
  · exact weight146_contains
  · exact weight147_contains
  · exact weight148_contains
  · exact weight149_contains
  · exact weight150_contains
  · exact weight151_contains
  · exact weight152_contains
  · exact weight153_contains
  · exact weight154_contains
  · exact weight155_contains
  · exact weight156_contains
  · exact weight157_contains
  · exact weight158_contains
  · exact weight159_contains
def weights10 : Fin 16 → RBox := ![weight160,weight161,weight162,weight163,weight164,weight165,weight166,weight167,weight168,weight169,weight170,weight171,weight172,weight173,weight174,weight175]
lemma weights10_contains (j : Fin 16) : (weights10 j).Contains (fejerWeight (160+j.val)) := by
  fin_cases j
  · exact weight160_contains
  · exact weight161_contains
  · exact weight162_contains
  · exact weight163_contains
  · exact weight164_contains
  · exact weight165_contains
  · exact weight166_contains
  · exact weight167_contains
  · exact weight168_contains
  · exact weight169_contains
  · exact weight170_contains
  · exact weight171_contains
  · exact weight172_contains
  · exact weight173_contains
  · exact weight174_contains
  · exact weight175_contains
def weights11 : Fin 16 → RBox := ![weight176,weight177,weight178,weight179,weight180,weight181,weight182,weight183,weight184,weight185,weight186,weight187,weight188,weight189,weight190,weight191]
lemma weights11_contains (j : Fin 16) : (weights11 j).Contains (fejerWeight (176+j.val)) := by
  fin_cases j
  · exact weight176_contains
  · exact weight177_contains
  · exact weight178_contains
  · exact weight179_contains
  · exact weight180_contains
  · exact weight181_contains
  · exact weight182_contains
  · exact weight183_contains
  · exact weight184_contains
  · exact weight185_contains
  · exact weight186_contains
  · exact weight187_contains
  · exact weight188_contains
  · exact weight189_contains
  · exact weight190_contains
  · exact weight191_contains
def weights12 : Fin 16 → RBox := ![weight192,weight193,weight194,weight195,weight196,weight197,weight198,weight199,weight200,weight201,weight202,weight203,weight204,weight205,weight206,weight207]
lemma weights12_contains (j : Fin 16) : (weights12 j).Contains (fejerWeight (192+j.val)) := by
  fin_cases j
  · exact weight192_contains
  · exact weight193_contains
  · exact weight194_contains
  · exact weight195_contains
  · exact weight196_contains
  · exact weight197_contains
  · exact weight198_contains
  · exact weight199_contains
  · exact weight200_contains
  · exact weight201_contains
  · exact weight202_contains
  · exact weight203_contains
  · exact weight204_contains
  · exact weight205_contains
  · exact weight206_contains
  · exact weight207_contains
def weights13 : Fin 16 → RBox := ![weight208,weight209,weight210,weight211,weight212,weight213,weight214,weight215,weight216,weight217,weight218,weight219,weight220,weight221,weight222,weight223]
lemma weights13_contains (j : Fin 16) : (weights13 j).Contains (fejerWeight (208+j.val)) := by
  fin_cases j
  · exact weight208_contains
  · exact weight209_contains
  · exact weight210_contains
  · exact weight211_contains
  · exact weight212_contains
  · exact weight213_contains
  · exact weight214_contains
  · exact weight215_contains
  · exact weight216_contains
  · exact weight217_contains
  · exact weight218_contains
  · exact weight219_contains
  · exact weight220_contains
  · exact weight221_contains
  · exact weight222_contains
  · exact weight223_contains
def weights14 : Fin 16 → RBox := ![weight224,weight225,weight226,weight227,weight228,weight229,weight230,weight231,weight232,weight233,weight234,weight235,weight236,weight237,weight238,weight239]
lemma weights14_contains (j : Fin 16) : (weights14 j).Contains (fejerWeight (224+j.val)) := by
  fin_cases j
  · exact weight224_contains
  · exact weight225_contains
  · exact weight226_contains
  · exact weight227_contains
  · exact weight228_contains
  · exact weight229_contains
  · exact weight230_contains
  · exact weight231_contains
  · exact weight232_contains
  · exact weight233_contains
  · exact weight234_contains
  · exact weight235_contains
  · exact weight236_contains
  · exact weight237_contains
  · exact weight238_contains
  · exact weight239_contains
def weights15 : Fin 16 → RBox := ![weight240,weight241,weight242,weight243,weight244,weight245,weight246,weight247,weight248,weight249,weight250,weight251,weight252,weight253,weight254,weight255]
lemma weights15_contains (j : Fin 16) : (weights15 j).Contains (fejerWeight (240+j.val)) := by
  fin_cases j
  · exact weight240_contains
  · exact weight241_contains
  · exact weight242_contains
  · exact weight243_contains
  · exact weight244_contains
  · exact weight245_contains
  · exact weight246_contains
  · exact weight247_contains
  · exact weight248_contains
  · exact weight249_contains
  · exact weight250_contains
  · exact weight251_contains
  · exact weight252_contains
  · exact weight253_contains
  · exact weight254_contains
  · exact weight255_contains
def weightRows : Fin 16 → Fin 16 → RBox := ![weights0,weights1,weights2,weights3,weights4,weights5,weights6,weights7,weights8,weights9,weights10,weights11,weights12,weights13,weights14,weights15]
lemma weightRows_contains (i j : Fin 16) : (weightRows i j).Contains (fejerWeight (16*i.val+j.val)) := by
  fin_cases i
  · exact weights0_contains j
  · exact weights1_contains j
  · exact weights2_contains j
  · exact weights3_contains j
  · exact weights4_contains j
  · exact weights5_contains j
  · exact weights6_contains j
  · exact weights7_contains j
  · exact weights8_contains j
  · exact weights9_contains j
  · exact weights10_contains j
  · exact weights11_contains j
  · exact weights12_contains j
  · exact weights13_contains j
  · exact weights14_contains j
  · exact weights15_contains j
def weightLookup (n : Fin 256) : RBox :=
  weightRows ⟨n.val/16,by omega⟩ ⟨n.val%16,by omega⟩
lemma weightLookup_contains (n : Fin 256) : (weightLookup n).Contains (fejerWeight n.val) := by
  have he : 16*(n.val/16)+n.val%16=n.val := by omega
  simpa only [weightLookup,he] using weightRows_contains ⟨n.val/16,by omega⟩ ⟨n.val%16,by omega⟩

def nodeLookup (n : Fin 256) : RBox := (rootLookup (2*n.val+1)).re
lemma nodeLookup_contains (n : Fin 256) : (nodeLookup n).Contains (fejerNode n.val) := by
  have hh := (rootLookup_contains (2*n.val+1)).1
  rw [rootPhase_mod,← fejerNode_root] at hh
  exact hh
end SharpPlanar.IntegerCompact


end OAI
