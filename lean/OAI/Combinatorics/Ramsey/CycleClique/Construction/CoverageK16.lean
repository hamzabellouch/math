import OAI.Combinatorics.Ramsey.CycleClique.Construction.CertificatesK16
import OAI.Combinatorics.Ramsey.CycleClique.Construction.CertificateCoverage

namespace OAI

namespace CycleClique.Construction.CertifiedCoverage

private theorem k16t8_cover15 : ∀ P ∈ pathPatterns 0 8 [], HasCheckedCertificate 16 8 ([[], [], [], [], [], [], [], []] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k16t8p0, Certificates.k16t8p0_check⟩

private theorem k16t8_cover14 : ∀ P ∈ pathPatterns 1 8 [], HasCheckedCertificate 16 8 ([[], [], [], [], [], [], []] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro _
      exact k16t8_cover15

private theorem k16t8_cover16 : ∀ P ∈ pathPatterns 0 7 [1], HasCheckedCertificate 16 8 ([[], [], [], [], [], [], [1]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k16t8p1, Certificates.k16t8p1_check⟩

private theorem k16t8_cover17 : ∀ P ∈ pathPatterns 0 6 [2], HasCheckedCertificate 16 8 ([[], [], [], [], [], [], [2]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k16t8p2, Certificates.k16t8p2_check⟩

private theorem k16t8_cover18 : ∀ P ∈ pathPatterns 0 5 [3], HasCheckedCertificate 16 8 ([[], [], [], [], [], [], [3]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k16t8p3, Certificates.k16t8p3_check⟩

private theorem k16t8_cover19 : ∀ P ∈ pathPatterns 0 4 [4], HasCheckedCertificate 16 8 ([[], [], [], [], [], [], [4]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k16t8p4, Certificates.k16t8p4_check⟩

private theorem k16t8_cover20 : ∀ P ∈ pathPatterns 0 3 [5], HasCheckedCertificate 16 8 ([[], [], [], [], [], [], [5]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k16t8p5, Certificates.k16t8p5_check⟩

private theorem k16t8_cover21 : ∀ P ∈ pathPatterns 0 2 [6], HasCheckedCertificate 16 8 ([[], [], [], [], [], [], [6]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k16t8p6, Certificates.k16t8p6_check⟩

private theorem k16t8_cover22 : ∀ P ∈ pathPatterns 0 1 [7], HasCheckedCertificate 16 8 ([[], [], [], [], [], [], [7]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k16t8p7, Certificates.k16t8p7_check⟩

private theorem k16t8_cover23 : ∀ P ∈ pathPatterns 0 0 [8], HasCheckedCertificate 16 8 ([[], [], [], [], [], [], [8]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k16t8p8, Certificates.k16t8p8_check⟩

private theorem k16t8_cover13 : ∀ P ∈ pathPatterns 2 8 [], HasCheckedCertificate 16 8 ([[], [], [], [], [], []] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro _
          exact k16t8_cover14
      · intro q
        fin_cases q
        · exact by
            intro _
            exact k16t8_cover16
        · exact by
            intro _
            exact k16t8_cover17
        · exact by
            intro _
            exact k16t8_cover18
        · exact by
            intro _
            exact k16t8_cover19
        · exact by
            intro _
            exact k16t8_cover20
        · exact by
            intro _
            exact k16t8_cover21
        · exact by
            intro _
            exact k16t8_cover22
        · exact by
            intro _
            exact k16t8_cover23

private theorem k16t8_cover24 : ∀ P ∈ pathPatterns 1 7 [1], HasCheckedCertificate 16 8 ([[], [], [], [], [], [1]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [1] [] ∧ LexLE [] [])) h)

private theorem k16t8_cover25 : ∀ P ∈ pathPatterns 0 6 [1, 1], HasCheckedCertificate 16 8 ([[], [], [], [], [], [1, 1]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k16t8p9, Certificates.k16t8p9_check⟩

private theorem k16t8_cover26 : ∀ P ∈ pathPatterns 0 5 [1, 2], HasCheckedCertificate 16 8 ([[], [], [], [], [], [1, 2]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k16t8p10, Certificates.k16t8p10_check⟩

private theorem k16t8_cover27 : ∀ P ∈ pathPatterns 0 4 [1, 3], HasCheckedCertificate 16 8 ([[], [], [], [], [], [1, 3]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k16t8p11, Certificates.k16t8p11_check⟩

private theorem k16t8_cover28 : ∀ P ∈ pathPatterns 0 3 [1, 4], HasCheckedCertificate 16 8 ([[], [], [], [], [], [1, 4]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k16t8p12, Certificates.k16t8p12_check⟩

private theorem k16t8_cover29 : ∀ P ∈ pathPatterns 0 2 [1, 5], HasCheckedCertificate 16 8 ([[], [], [], [], [], [1, 5]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k16t8p13, Certificates.k16t8p13_check⟩

private theorem k16t8_cover30 : ∀ P ∈ pathPatterns 0 1 [1, 6], HasCheckedCertificate 16 8 ([[], [], [], [], [], [1, 6]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k16t8p14, Certificates.k16t8p14_check⟩

private theorem k16t8_cover31 : ∀ P ∈ pathPatterns 0 0 [1, 7], HasCheckedCertificate 16 8 ([[], [], [], [], [], [1, 7]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k16t8p15, Certificates.k16t8p15_check⟩

private theorem k16t8_cover32 : ∀ P ∈ pathPatterns 1 6 [2], HasCheckedCertificate 16 8 ([[], [], [], [], [], [2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [2] [] ∧ LexLE [] [])) h)

private theorem k16t8_cover33 : ∀ P ∈ pathPatterns 0 4 [2, 2], HasCheckedCertificate 16 8 ([[], [], [], [], [], [2, 2]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k16t8p16, Certificates.k16t8p16_check⟩

private theorem k16t8_cover34 : ∀ P ∈ pathPatterns 0 3 [2, 3], HasCheckedCertificate 16 8 ([[], [], [], [], [], [2, 3]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k16t8p17, Certificates.k16t8p17_check⟩

private theorem k16t8_cover35 : ∀ P ∈ pathPatterns 0 2 [2, 4], HasCheckedCertificate 16 8 ([[], [], [], [], [], [2, 4]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k16t8p18, Certificates.k16t8p18_check⟩

private theorem k16t8_cover36 : ∀ P ∈ pathPatterns 0 1 [2, 5], HasCheckedCertificate 16 8 ([[], [], [], [], [], [2, 5]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k16t8p19, Certificates.k16t8p19_check⟩

private theorem k16t8_cover37 : ∀ P ∈ pathPatterns 0 0 [2, 6], HasCheckedCertificate 16 8 ([[], [], [], [], [], [2, 6]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k16t8p20, Certificates.k16t8p20_check⟩

private theorem k16t8_cover38 : ∀ P ∈ pathPatterns 1 5 [3], HasCheckedCertificate 16 8 ([[], [], [], [], [], [3]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [3] [] ∧ LexLE [] [])) h)

private theorem k16t8_cover39 : ∀ P ∈ pathPatterns 0 2 [3, 3], HasCheckedCertificate 16 8 ([[], [], [], [], [], [3, 3]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k16t8p21, Certificates.k16t8p21_check⟩

private theorem k16t8_cover40 : ∀ P ∈ pathPatterns 0 1 [3, 4], HasCheckedCertificate 16 8 ([[], [], [], [], [], [3, 4]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k16t8p22, Certificates.k16t8p22_check⟩

private theorem k16t8_cover41 : ∀ P ∈ pathPatterns 0 0 [3, 5], HasCheckedCertificate 16 8 ([[], [], [], [], [], [3, 5]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k16t8p23, Certificates.k16t8p23_check⟩

private theorem k16t8_cover42 : ∀ P ∈ pathPatterns 1 4 [4], HasCheckedCertificate 16 8 ([[], [], [], [], [], [4]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [4] [] ∧ LexLE [] [])) h)

private theorem k16t8_cover43 : ∀ P ∈ pathPatterns 0 0 [4, 4], HasCheckedCertificate 16 8 ([[], [], [], [], [], [4, 4]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k16t8p24, Certificates.k16t8p24_check⟩

private theorem k16t8_cover44 : ∀ P ∈ pathPatterns 1 3 [5], HasCheckedCertificate 16 8 ([[], [], [], [], [], [5]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [5] [] ∧ LexLE [] [])) h)

private theorem k16t8_cover45 : ∀ P ∈ pathPatterns 1 2 [6], HasCheckedCertificate 16 8 ([[], [], [], [], [], [6]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [6] [] ∧ LexLE [] [])) h)

private theorem k16t8_cover46 : ∀ P ∈ pathPatterns 1 1 [7], HasCheckedCertificate 16 8 ([[], [], [], [], [], [7]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [7] [] ∧ LexLE [] [])) h)

private theorem k16t8_cover47 : ∀ P ∈ pathPatterns 1 0 [8], HasCheckedCertificate 16 8 ([[], [], [], [], [], [8]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [8] [] ∧ LexLE [] [])) h)

private theorem k16t8_seq12 : amountSequenceForall 2 8 (fun tail =>
    (LexLE [] ([] ++ tail) ∧ LexLE ([] ++ tail) ([] ++ tail).reverse) →
    ∀ P ∈ pathPatterns (2 - ([] ++ tail).length) (8 - ([] ++ tail).sum) ([] ++ tail),
      HasCheckedCertificate 16 8 ([[], [], [], [], []] ++ (([] ++ tail) :: P))) :=
by
  constructor
  · exact by
      intro _
      exact k16t8_cover13
  · intro q
    fin_cases q
    · exact by
        constructor
        · exact by
            intro _
            exact k16t8_cover24
        · intro q
          fin_cases q
          · exact by
              intro _
              exact k16t8_cover25
          · exact by
              intro _
              exact k16t8_cover26
          · exact by
              intro _
              exact k16t8_cover27
          · exact by
              intro _
              exact k16t8_cover28
          · exact by
              intro _
              exact k16t8_cover29
          · exact by
              intro _
              exact k16t8_cover30
          · exact by
              intro _
              exact k16t8_cover31
    · exact by
        constructor
        · exact by
            intro _
            exact k16t8_cover32
        · intro q
          fin_cases q
          · exact by
              intro h
              exact False.elim ((by decide : ¬ (LexLE [] [2, 1] ∧ LexLE [2, 1] [1, 2])) h)
          · exact by
              intro _
              exact k16t8_cover33
          · exact by
              intro _
              exact k16t8_cover34
          · exact by
              intro _
              exact k16t8_cover35
          · exact by
              intro _
              exact k16t8_cover36
          · exact by
              intro _
              exact k16t8_cover37
    · exact by
        constructor
        · exact by
            intro _
            exact k16t8_cover38
        · intro q
          fin_cases q
          · exact by
              intro h
              exact False.elim ((by decide : ¬ (LexLE [] [3, 1] ∧ LexLE [3, 1] [1, 3])) h)
          · exact by
              intro h
              exact False.elim ((by decide : ¬ (LexLE [] [3, 2] ∧ LexLE [3, 2] [2, 3])) h)
          · exact by
              intro _
              exact k16t8_cover39
          · exact by
              intro _
              exact k16t8_cover40
          · exact by
              intro _
              exact k16t8_cover41
    · exact by
        constructor
        · exact by
            intro _
            exact k16t8_cover42
        · intro q
          fin_cases q
          · exact by
              intro h
              exact False.elim ((by decide : ¬ (LexLE [] [4, 1] ∧ LexLE [4, 1] [1, 4])) h)
          · exact by
              intro h
              exact False.elim ((by decide : ¬ (LexLE [] [4, 2] ∧ LexLE [4, 2] [2, 4])) h)
          · exact by
              intro h
              exact False.elim ((by decide : ¬ (LexLE [] [4, 3] ∧ LexLE [4, 3] [3, 4])) h)
          · exact by
              intro _
              exact k16t8_cover43
    · exact by
        constructor
        · exact by
            intro _
            exact k16t8_cover44
        · intro q
          fin_cases q
          · exact by
              intro h
              exact False.elim ((by decide : ¬ (LexLE [] [5, 1] ∧ LexLE [5, 1] [1, 5])) h)
          · exact by
              intro h
              exact False.elim ((by decide : ¬ (LexLE [] [5, 2] ∧ LexLE [5, 2] [2, 5])) h)
          · exact by
              intro h
              exact False.elim ((by decide : ¬ (LexLE [] [5, 3] ∧ LexLE [5, 3] [3, 5])) h)
    · exact by
        constructor
        · exact by
            intro _
            exact k16t8_cover45
        · intro q
          fin_cases q
          · exact by
              intro h
              exact False.elim ((by decide : ¬ (LexLE [] [6, 1] ∧ LexLE [6, 1] [1, 6])) h)
          · exact by
              intro h
              exact False.elim ((by decide : ¬ (LexLE [] [6, 2] ∧ LexLE [6, 2] [2, 6])) h)
    · exact by
        constructor
        · exact by
            intro _
            exact k16t8_cover46
        · intro q
          fin_cases q
          · exact by
              intro h
              exact False.elim ((by decide : ¬ (LexLE [] [7, 1] ∧ LexLE [7, 1] [1, 7])) h)
    · exact by
        constructor
        · exact by
            intro _
            exact k16t8_cover47
        · intro q
          exact Fin.elim0 q

private theorem k16t8_cover11 : ∀ P ∈ pathPatterns 3 8 [], HasCheckedCertificate 16 8 ([[], [], [], [], []] ++ P) := by
  apply pathPatterns_forall_step
  exact k16t8_seq12


private theorem k16t8_cover50 : ∀ P ∈ pathPatterns 0 6 [1], HasCheckedCertificate 16 8 ([[], [], [], [], [1], [1]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k16t8p25, Certificates.k16t8p25_check⟩

private theorem k16t8_cover51 : ∀ P ∈ pathPatterns 0 5 [2], HasCheckedCertificate 16 8 ([[], [], [], [], [1], [2]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k16t8p26, Certificates.k16t8p26_check⟩

private theorem k16t8_cover52 : ∀ P ∈ pathPatterns 0 4 [3], HasCheckedCertificate 16 8 ([[], [], [], [], [1], [3]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k16t8p27, Certificates.k16t8p27_check⟩

private theorem k16t8_cover53 : ∀ P ∈ pathPatterns 0 3 [4], HasCheckedCertificate 16 8 ([[], [], [], [], [1], [4]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k16t8p28, Certificates.k16t8p28_check⟩

private theorem k16t8_cover54 : ∀ P ∈ pathPatterns 0 2 [5], HasCheckedCertificate 16 8 ([[], [], [], [], [1], [5]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k16t8p29, Certificates.k16t8p29_check⟩

private theorem k16t8_cover55 : ∀ P ∈ pathPatterns 0 1 [6], HasCheckedCertificate 16 8 ([[], [], [], [], [1], [6]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k16t8p30, Certificates.k16t8p30_check⟩

private theorem k16t8_cover56 : ∀ P ∈ pathPatterns 0 0 [7], HasCheckedCertificate 16 8 ([[], [], [], [], [1], [7]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k16t8p31, Certificates.k16t8p31_check⟩

private theorem k16t8_cover49 : ∀ P ∈ pathPatterns 2 7 [1], HasCheckedCertificate 16 8 ([[], [], [], [], [1]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [1] [] ∧ LexLE [] [])) h)
      · intro q
        fin_cases q
        · exact by
            intro _
            exact k16t8_cover50
        · exact by
            intro _
            exact k16t8_cover51
        · exact by
            intro _
            exact k16t8_cover52
        · exact by
            intro _
            exact k16t8_cover53
        · exact by
            intro _
            exact k16t8_cover54
        · exact by
            intro _
            exact k16t8_cover55
        · exact by
            intro _
            exact k16t8_cover56

private theorem k16t8_cover57 : ∀ P ∈ pathPatterns 1 6 [1, 1], HasCheckedCertificate 16 8 ([[], [], [], [], [1, 1]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [1, 1] [] ∧ LexLE [] [])) h)

private theorem k16t8_cover58 : ∀ P ∈ pathPatterns 0 5 [1, 1, 1], HasCheckedCertificate 16 8 ([[], [], [], [], [1, 1, 1]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k16t8p32, Certificates.k16t8p32_check⟩

private theorem k16t8_cover59 : ∀ P ∈ pathPatterns 0 4 [1, 1, 2], HasCheckedCertificate 16 8 ([[], [], [], [], [1, 1, 2]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k16t8p33, Certificates.k16t8p33_check⟩

private theorem k16t8_cover60 : ∀ P ∈ pathPatterns 0 3 [1, 1, 3], HasCheckedCertificate 16 8 ([[], [], [], [], [1, 1, 3]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k16t8p34, Certificates.k16t8p34_check⟩

private theorem k16t8_cover61 : ∀ P ∈ pathPatterns 0 2 [1, 1, 4], HasCheckedCertificate 16 8 ([[], [], [], [], [1, 1, 4]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k16t8p35, Certificates.k16t8p35_check⟩

private theorem k16t8_cover62 : ∀ P ∈ pathPatterns 0 1 [1, 1, 5], HasCheckedCertificate 16 8 ([[], [], [], [], [1, 1, 5]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k16t8p36, Certificates.k16t8p36_check⟩

private theorem k16t8_cover63 : ∀ P ∈ pathPatterns 0 0 [1, 1, 6], HasCheckedCertificate 16 8 ([[], [], [], [], [1, 1, 6]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k16t8p37, Certificates.k16t8p37_check⟩

private theorem k16t8_cover64 : ∀ P ∈ pathPatterns 1 5 [1, 2], HasCheckedCertificate 16 8 ([[], [], [], [], [1, 2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [1, 2] [] ∧ LexLE [] [])) h)

private theorem k16t8_cover65 : ∀ P ∈ pathPatterns 0 4 [1, 2, 1], HasCheckedCertificate 16 8 ([[], [], [], [], [1, 2, 1]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k16t8p38, Certificates.k16t8p38_check⟩

private theorem k16t8_cover66 : ∀ P ∈ pathPatterns 0 3 [1, 2, 2], HasCheckedCertificate 16 8 ([[], [], [], [], [1, 2, 2]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k16t8p39, Certificates.k16t8p39_check⟩

private theorem k16t8_cover67 : ∀ P ∈ pathPatterns 0 2 [1, 2, 3], HasCheckedCertificate 16 8 ([[], [], [], [], [1, 2, 3]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k16t8p40, Certificates.k16t8p40_check⟩

private theorem k16t8_cover68 : ∀ P ∈ pathPatterns 0 1 [1, 2, 4], HasCheckedCertificate 16 8 ([[], [], [], [], [1, 2, 4]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k16t8p41, Certificates.k16t8p41_check⟩

private theorem k16t8_cover69 : ∀ P ∈ pathPatterns 0 0 [1, 2, 5], HasCheckedCertificate 16 8 ([[], [], [], [], [1, 2, 5]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k16t8p42, Certificates.k16t8p42_check⟩

private theorem k16t8_cover70 : ∀ P ∈ pathPatterns 1 4 [1, 3], HasCheckedCertificate 16 8 ([[], [], [], [], [1, 3]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [1, 3] [] ∧ LexLE [] [])) h)

private theorem k16t8_cover71 : ∀ P ∈ pathPatterns 0 3 [1, 3, 1], HasCheckedCertificate 16 8 ([[], [], [], [], [1, 3, 1]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k16t8p43, Certificates.k16t8p43_check⟩

private theorem k16t8_cover72 : ∀ P ∈ pathPatterns 0 2 [1, 3, 2], HasCheckedCertificate 16 8 ([[], [], [], [], [1, 3, 2]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k16t8p44, Certificates.k16t8p44_check⟩

private theorem k16t8_cover73 : ∀ P ∈ pathPatterns 0 1 [1, 3, 3], HasCheckedCertificate 16 8 ([[], [], [], [], [1, 3, 3]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k16t8p45, Certificates.k16t8p45_check⟩

private theorem k16t8_cover74 : ∀ P ∈ pathPatterns 0 0 [1, 3, 4], HasCheckedCertificate 16 8 ([[], [], [], [], [1, 3, 4]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k16t8p46, Certificates.k16t8p46_check⟩

private theorem k16t8_cover75 : ∀ P ∈ pathPatterns 1 3 [1, 4], HasCheckedCertificate 16 8 ([[], [], [], [], [1, 4]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [1, 4] [] ∧ LexLE [] [])) h)

private theorem k16t8_cover76 : ∀ P ∈ pathPatterns 0 2 [1, 4, 1], HasCheckedCertificate 16 8 ([[], [], [], [], [1, 4, 1]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k16t8p47, Certificates.k16t8p47_check⟩

private theorem k16t8_cover77 : ∀ P ∈ pathPatterns 0 1 [1, 4, 2], HasCheckedCertificate 16 8 ([[], [], [], [], [1, 4, 2]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k16t8p48, Certificates.k16t8p48_check⟩

private theorem k16t8_cover78 : ∀ P ∈ pathPatterns 0 0 [1, 4, 3], HasCheckedCertificate 16 8 ([[], [], [], [], [1, 4, 3]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k16t8p49, Certificates.k16t8p49_check⟩

private theorem k16t8_cover79 : ∀ P ∈ pathPatterns 1 2 [1, 5], HasCheckedCertificate 16 8 ([[], [], [], [], [1, 5]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [1, 5] [] ∧ LexLE [] [])) h)

private theorem k16t8_cover80 : ∀ P ∈ pathPatterns 0 1 [1, 5, 1], HasCheckedCertificate 16 8 ([[], [], [], [], [1, 5, 1]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k16t8p50, Certificates.k16t8p50_check⟩

private theorem k16t8_cover81 : ∀ P ∈ pathPatterns 0 0 [1, 5, 2], HasCheckedCertificate 16 8 ([[], [], [], [], [1, 5, 2]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k16t8p51, Certificates.k16t8p51_check⟩

private theorem k16t8_cover82 : ∀ P ∈ pathPatterns 1 1 [1, 6], HasCheckedCertificate 16 8 ([[], [], [], [], [1, 6]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [1, 6] [] ∧ LexLE [] [])) h)

private theorem k16t8_cover83 : ∀ P ∈ pathPatterns 0 0 [1, 6, 1], HasCheckedCertificate 16 8 ([[], [], [], [], [1, 6, 1]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k16t8p52, Certificates.k16t8p52_check⟩

private theorem k16t8_cover84 : ∀ P ∈ pathPatterns 1 0 [1, 7], HasCheckedCertificate 16 8 ([[], [], [], [], [1, 7]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [1, 7] [] ∧ LexLE [] [])) h)

private theorem k16t8_seq48 : amountSequenceForall 2 7 (fun tail =>
    (LexLE [] ([1] ++ tail) ∧ LexLE ([1] ++ tail) ([1] ++ tail).reverse) →
    ∀ P ∈ pathPatterns (3 - ([1] ++ tail).length) (8 - ([1] ++ tail).sum) ([1] ++ tail),
      HasCheckedCertificate 16 8 ([[], [], [], []] ++ (([1] ++ tail) :: P))) :=
by
  constructor
  · exact by
      intro _
      exact k16t8_cover49
  · intro q
    fin_cases q
    · exact by
        constructor
        · exact by
            intro _
            exact k16t8_cover57
        · intro q
          fin_cases q
          · exact by
              intro _
              exact k16t8_cover58
          · exact by
              intro _
              exact k16t8_cover59
          · exact by
              intro _
              exact k16t8_cover60
          · exact by
              intro _
              exact k16t8_cover61
          · exact by
              intro _
              exact k16t8_cover62
          · exact by
              intro _
              exact k16t8_cover63
    · exact by
        constructor
        · exact by
            intro _
            exact k16t8_cover64
        · intro q
          fin_cases q
          · exact by
              intro _
              exact k16t8_cover65
          · exact by
              intro _
              exact k16t8_cover66
          · exact by
              intro _
              exact k16t8_cover67
          · exact by
              intro _
              exact k16t8_cover68
          · exact by
              intro _
              exact k16t8_cover69
    · exact by
        constructor
        · exact by
            intro _
            exact k16t8_cover70
        · intro q
          fin_cases q
          · exact by
              intro _
              exact k16t8_cover71
          · exact by
              intro _
              exact k16t8_cover72
          · exact by
              intro _
              exact k16t8_cover73
          · exact by
              intro _
              exact k16t8_cover74
    · exact by
        constructor
        · exact by
            intro _
            exact k16t8_cover75
        · intro q
          fin_cases q
          · exact by
              intro _
              exact k16t8_cover76
          · exact by
              intro _
              exact k16t8_cover77
          · exact by
              intro _
              exact k16t8_cover78
    · exact by
        constructor
        · exact by
            intro _
            exact k16t8_cover79
        · intro q
          fin_cases q
          · exact by
              intro _
              exact k16t8_cover80
          · exact by
              intro _
              exact k16t8_cover81
    · exact by
        constructor
        · exact by
            intro _
            exact k16t8_cover82
        · intro q
          fin_cases q
          · exact by
              intro _
              exact k16t8_cover83
    · exact by
        constructor
        · exact by
            intro _
            exact k16t8_cover84
        · intro q
          exact Fin.elim0 q

private theorem k16t8_cover86 : ∀ P ∈ pathPatterns 0 4 [2], HasCheckedCertificate 16 8 ([[], [], [], [], [2], [2]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k16t8p53, Certificates.k16t8p53_check⟩

private theorem k16t8_cover87 : ∀ P ∈ pathPatterns 0 3 [3], HasCheckedCertificate 16 8 ([[], [], [], [], [2], [3]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k16t8p54, Certificates.k16t8p54_check⟩

private theorem k16t8_cover88 : ∀ P ∈ pathPatterns 0 2 [4], HasCheckedCertificate 16 8 ([[], [], [], [], [2], [4]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k16t8p55, Certificates.k16t8p55_check⟩

private theorem k16t8_cover89 : ∀ P ∈ pathPatterns 0 1 [5], HasCheckedCertificate 16 8 ([[], [], [], [], [2], [5]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k16t8p56, Certificates.k16t8p56_check⟩

private theorem k16t8_cover90 : ∀ P ∈ pathPatterns 0 0 [6], HasCheckedCertificate 16 8 ([[], [], [], [], [2], [6]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k16t8p57, Certificates.k16t8p57_check⟩

private theorem k16t8_cover85 : ∀ P ∈ pathPatterns 2 6 [2], HasCheckedCertificate 16 8 ([[], [], [], [], [2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [2] [] ∧ LexLE [] [])) h)
      · intro q
        fin_cases q
        · exact by
            intro h
            exact False.elim ((by decide : ¬ (LexLE [2] [1] ∧ LexLE [1] [1])) h)
        · exact by
            intro _
            exact k16t8_cover86
        · exact by
            intro _
            exact k16t8_cover87
        · exact by
            intro _
            exact k16t8_cover88
        · exact by
            intro _
            exact k16t8_cover89
        · exact by
            intro _
            exact k16t8_cover90

private theorem k16t8_cover91 : ∀ P ∈ pathPatterns 0 3 [2, 1, 2], HasCheckedCertificate 16 8 ([[], [], [], [], [2, 1, 2]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k16t8p58, Certificates.k16t8p58_check⟩

private theorem k16t8_cover92 : ∀ P ∈ pathPatterns 0 2 [2, 1, 3], HasCheckedCertificate 16 8 ([[], [], [], [], [2, 1, 3]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k16t8p59, Certificates.k16t8p59_check⟩

private theorem k16t8_cover93 : ∀ P ∈ pathPatterns 0 1 [2, 1, 4], HasCheckedCertificate 16 8 ([[], [], [], [], [2, 1, 4]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k16t8p60, Certificates.k16t8p60_check⟩

private theorem k16t8_cover94 : ∀ P ∈ pathPatterns 0 0 [2, 1, 5], HasCheckedCertificate 16 8 ([[], [], [], [], [2, 1, 5]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k16t8p61, Certificates.k16t8p61_check⟩

private theorem k16t8_cover95 : ∀ P ∈ pathPatterns 1 4 [2, 2], HasCheckedCertificate 16 8 ([[], [], [], [], [2, 2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [2, 2] [] ∧ LexLE [] [])) h)

private theorem k16t8_cover96 : ∀ P ∈ pathPatterns 0 2 [2, 2, 2], HasCheckedCertificate 16 8 ([[], [], [], [], [2, 2, 2]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k16t8p62, Certificates.k16t8p62_check⟩

private theorem k16t8_cover97 : ∀ P ∈ pathPatterns 0 1 [2, 2, 3], HasCheckedCertificate 16 8 ([[], [], [], [], [2, 2, 3]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k16t8p63, Certificates.k16t8p63_check⟩

private theorem k16t8_cover98 : ∀ P ∈ pathPatterns 0 0 [2, 2, 4], HasCheckedCertificate 16 8 ([[], [], [], [], [2, 2, 4]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k16t8p64, Certificates.k16t8p64_check⟩

private theorem k16t8_cover99 : ∀ P ∈ pathPatterns 1 3 [2, 3], HasCheckedCertificate 16 8 ([[], [], [], [], [2, 3]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [2, 3] [] ∧ LexLE [] [])) h)

private theorem k16t8_cover100 : ∀ P ∈ pathPatterns 0 1 [2, 3, 2], HasCheckedCertificate 16 8 ([[], [], [], [], [2, 3, 2]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k16t8p65, Certificates.k16t8p65_check⟩

private theorem k16t8_cover101 : ∀ P ∈ pathPatterns 0 0 [2, 3, 3], HasCheckedCertificate 16 8 ([[], [], [], [], [2, 3, 3]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k16t8p66, Certificates.k16t8p66_check⟩

private theorem k16t8_cover102 : ∀ P ∈ pathPatterns 1 2 [2, 4], HasCheckedCertificate 16 8 ([[], [], [], [], [2, 4]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [2, 4] [] ∧ LexLE [] [])) h)

private theorem k16t8_cover103 : ∀ P ∈ pathPatterns 0 0 [2, 4, 2], HasCheckedCertificate 16 8 ([[], [], [], [], [2, 4, 2]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k16t8p67, Certificates.k16t8p67_check⟩

private theorem k16t8_cover104 : ∀ P ∈ pathPatterns 1 1 [2, 5], HasCheckedCertificate 16 8 ([[], [], [], [], [2, 5]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [2, 5] [] ∧ LexLE [] [])) h)

private theorem k16t8_cover105 : ∀ P ∈ pathPatterns 1 0 [2, 6], HasCheckedCertificate 16 8 ([[], [], [], [], [2, 6]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [2, 6] [] ∧ LexLE [] [])) h)

private theorem k16t8_cover107 : ∀ P ∈ pathPatterns 0 2 [3], HasCheckedCertificate 16 8 ([[], [], [], [], [3], [3]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k16t8p68, Certificates.k16t8p68_check⟩

private theorem k16t8_cover108 : ∀ P ∈ pathPatterns 0 1 [4], HasCheckedCertificate 16 8 ([[], [], [], [], [3], [4]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k16t8p69, Certificates.k16t8p69_check⟩

private theorem k16t8_cover109 : ∀ P ∈ pathPatterns 0 0 [5], HasCheckedCertificate 16 8 ([[], [], [], [], [3], [5]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k16t8p70, Certificates.k16t8p70_check⟩

private theorem k16t8_cover106 : ∀ P ∈ pathPatterns 2 5 [3], HasCheckedCertificate 16 8 ([[], [], [], [], [3]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [3] [] ∧ LexLE [] [])) h)
      · intro q
        fin_cases q
        · exact by
            intro h
            exact False.elim ((by decide : ¬ (LexLE [3] [1] ∧ LexLE [1] [1])) h)
        · exact by
            intro h
            exact False.elim ((by decide : ¬ (LexLE [3] [2] ∧ LexLE [2] [2])) h)
        · exact by
            intro _
            exact k16t8_cover107
        · exact by
            intro _
            exact k16t8_cover108
        · exact by
            intro _
            exact k16t8_cover109

private theorem k16t8_cover110 : ∀ P ∈ pathPatterns 0 1 [3, 1, 3], HasCheckedCertificate 16 8 ([[], [], [], [], [3, 1, 3]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k16t8p71, Certificates.k16t8p71_check⟩

private theorem k16t8_cover111 : ∀ P ∈ pathPatterns 0 0 [3, 1, 4], HasCheckedCertificate 16 8 ([[], [], [], [], [3, 1, 4]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k16t8p72, Certificates.k16t8p72_check⟩

private theorem k16t8_cover112 : ∀ P ∈ pathPatterns 0 0 [3, 2, 3], HasCheckedCertificate 16 8 ([[], [], [], [], [3, 2, 3]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k16t8p73, Certificates.k16t8p73_check⟩

private theorem k16t8_cover113 : ∀ P ∈ pathPatterns 1 2 [3, 3], HasCheckedCertificate 16 8 ([[], [], [], [], [3, 3]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [3, 3] [] ∧ LexLE [] [])) h)

private theorem k16t8_cover114 : ∀ P ∈ pathPatterns 1 1 [3, 4], HasCheckedCertificate 16 8 ([[], [], [], [], [3, 4]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [3, 4] [] ∧ LexLE [] [])) h)

private theorem k16t8_cover115 : ∀ P ∈ pathPatterns 1 0 [3, 5], HasCheckedCertificate 16 8 ([[], [], [], [], [3, 5]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [3, 5] [] ∧ LexLE [] [])) h)

private theorem k16t8_cover117 : ∀ P ∈ pathPatterns 0 0 [4], HasCheckedCertificate 16 8 ([[], [], [], [], [4], [4]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k16t8p74, Certificates.k16t8p74_check⟩

private theorem k16t8_cover116 : ∀ P ∈ pathPatterns 2 4 [4], HasCheckedCertificate 16 8 ([[], [], [], [], [4]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [4] [] ∧ LexLE [] [])) h)
      · intro q
        fin_cases q
        · exact by
            intro h
            exact False.elim ((by decide : ¬ (LexLE [4] [1] ∧ LexLE [1] [1])) h)
        · exact by
            intro h
            exact False.elim ((by decide : ¬ (LexLE [4] [2] ∧ LexLE [2] [2])) h)
        · exact by
            intro h
            exact False.elim ((by decide : ¬ (LexLE [4] [3] ∧ LexLE [3] [3])) h)
        · exact by
            intro _
            exact k16t8_cover117

private theorem k16t8_cover118 : ∀ P ∈ pathPatterns 1 0 [4, 4], HasCheckedCertificate 16 8 ([[], [], [], [], [4, 4]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [4, 4] [] ∧ LexLE [] [])) h)

private theorem k16t8_cover119 : ∀ P ∈ pathPatterns 2 3 [5], HasCheckedCertificate 16 8 ([[], [], [], [], [5]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [5] [] ∧ LexLE [] [])) h)
      · intro q
        fin_cases q
        · exact by
            intro h
            exact False.elim ((by decide : ¬ (LexLE [5] [1] ∧ LexLE [1] [1])) h)
        · exact by
            intro h
            exact False.elim ((by decide : ¬ (LexLE [5] [2] ∧ LexLE [2] [2])) h)
        · exact by
            intro h
            exact False.elim ((by decide : ¬ (LexLE [5] [3] ∧ LexLE [3] [3])) h)

private theorem k16t8_cover120 : ∀ P ∈ pathPatterns 2 2 [6], HasCheckedCertificate 16 8 ([[], [], [], [], [6]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [6] [] ∧ LexLE [] [])) h)
      · intro q
        fin_cases q
        · exact by
            intro h
            exact False.elim ((by decide : ¬ (LexLE [6] [1] ∧ LexLE [1] [1])) h)
        · exact by
            intro h
            exact False.elim ((by decide : ¬ (LexLE [6] [2] ∧ LexLE [2] [2])) h)

private theorem k16t8_cover121 : ∀ P ∈ pathPatterns 2 1 [7], HasCheckedCertificate 16 8 ([[], [], [], [], [7]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [7] [] ∧ LexLE [] [])) h)
      · intro q
        fin_cases q
        · exact by
            intro h
            exact False.elim ((by decide : ¬ (LexLE [7] [1] ∧ LexLE [1] [1])) h)

private theorem k16t8_cover122 : ∀ P ∈ pathPatterns 2 0 [8], HasCheckedCertificate 16 8 ([[], [], [], [], [8]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [8] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k16t8_seq10 : amountSequenceForall 3 8 (fun tail =>
    (LexLE [] ([] ++ tail) ∧ LexLE ([] ++ tail) ([] ++ tail).reverse) →
    ∀ P ∈ pathPatterns (3 - ([] ++ tail).length) (8 - ([] ++ tail).sum) ([] ++ tail),
      HasCheckedCertificate 16 8 ([[], [], [], []] ++ (([] ++ tail) :: P))) :=
by
  constructor
  · exact by
      intro _
      exact k16t8_cover11
  · intro q
    fin_cases q
    · exact k16t8_seq48

    · exact by
        constructor
        · exact by
            intro _
            exact k16t8_cover85
        · intro q
          fin_cases q
          · exact by
              constructor
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [] [2, 1] ∧ LexLE [2, 1] [1, 2])) h)
              · intro q
                fin_cases q
                · exact by
                    intro h
                    exact False.elim ((by decide : ¬ (LexLE [] [2, 1, 1] ∧ LexLE [2, 1, 1] [1, 1, 2])) h)
                · exact by
                    intro _
                    exact k16t8_cover91
                · exact by
                    intro _
                    exact k16t8_cover92
                · exact by
                    intro _
                    exact k16t8_cover93
                · exact by
                    intro _
                    exact k16t8_cover94
          · exact by
              constructor
              · exact by
                  intro _
                  exact k16t8_cover95
              · intro q
                fin_cases q
                · exact by
                    intro h
                    exact False.elim ((by decide : ¬ (LexLE [] [2, 2, 1] ∧ LexLE [2, 2, 1] [1, 2, 2])) h)
                · exact by
                    intro _
                    exact k16t8_cover96
                · exact by
                    intro _
                    exact k16t8_cover97
                · exact by
                    intro _
                    exact k16t8_cover98
          · exact by
              constructor
              · exact by
                  intro _
                  exact k16t8_cover99
              · intro q
                fin_cases q
                · exact by
                    intro h
                    exact False.elim ((by decide : ¬ (LexLE [] [2, 3, 1] ∧ LexLE [2, 3, 1] [1, 3, 2])) h)
                · exact by
                    intro _
                    exact k16t8_cover100
                · exact by
                    intro _
                    exact k16t8_cover101
          · exact by
              constructor
              · exact by
                  intro _
                  exact k16t8_cover102
              · intro q
                fin_cases q
                · exact by
                    intro h
                    exact False.elim ((by decide : ¬ (LexLE [] [2, 4, 1] ∧ LexLE [2, 4, 1] [1, 4, 2])) h)
                · exact by
                    intro _
                    exact k16t8_cover103
          · exact by
              constructor
              · exact by
                  intro _
                  exact k16t8_cover104
              · intro q
                fin_cases q
                · exact by
                    intro h
                    exact False.elim ((by decide : ¬ (LexLE [] [2, 5, 1] ∧ LexLE [2, 5, 1] [1, 5, 2])) h)
          · exact by
              constructor
              · exact by
                  intro _
                  exact k16t8_cover105
              · intro q
                exact Fin.elim0 q
    · exact by
        constructor
        · exact by
            intro _
            exact k16t8_cover106
        · intro q
          fin_cases q
          · exact by
              constructor
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [] [3, 1] ∧ LexLE [3, 1] [1, 3])) h)
              · intro q
                fin_cases q
                · exact by
                    intro h
                    exact False.elim ((by decide : ¬ (LexLE [] [3, 1, 1] ∧ LexLE [3, 1, 1] [1, 1, 3])) h)
                · exact by
                    intro h
                    exact False.elim ((by decide : ¬ (LexLE [] [3, 1, 2] ∧ LexLE [3, 1, 2] [2, 1, 3])) h)
                · exact by
                    intro _
                    exact k16t8_cover110
                · exact by
                    intro _
                    exact k16t8_cover111
          · exact by
              constructor
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [] [3, 2] ∧ LexLE [3, 2] [2, 3])) h)
              · intro q
                fin_cases q
                · exact by
                    intro h
                    exact False.elim ((by decide : ¬ (LexLE [] [3, 2, 1] ∧ LexLE [3, 2, 1] [1, 2, 3])) h)
                · exact by
                    intro h
                    exact False.elim ((by decide : ¬ (LexLE [] [3, 2, 2] ∧ LexLE [3, 2, 2] [2, 2, 3])) h)
                · exact by
                    intro _
                    exact k16t8_cover112
          · exact by
              constructor
              · exact by
                  intro _
                  exact k16t8_cover113
              · intro q
                fin_cases q
                · exact by
                    intro h
                    exact False.elim ((by decide : ¬ (LexLE [] [3, 3, 1] ∧ LexLE [3, 3, 1] [1, 3, 3])) h)
                · exact by
                    intro h
                    exact False.elim ((by decide : ¬ (LexLE [] [3, 3, 2] ∧ LexLE [3, 3, 2] [2, 3, 3])) h)
          · exact by
              constructor
              · exact by
                  intro _
                  exact k16t8_cover114
              · intro q
                fin_cases q
                · exact by
                    intro h
                    exact False.elim ((by decide : ¬ (LexLE [] [3, 4, 1] ∧ LexLE [3, 4, 1] [1, 4, 3])) h)
          · exact by
              constructor
              · exact by
                  intro _
                  exact k16t8_cover115
              · intro q
                exact Fin.elim0 q
    · exact by
        constructor
        · exact by
            intro _
            exact k16t8_cover116
        · intro q
          fin_cases q
          · exact by
              constructor
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [] [4, 1] ∧ LexLE [4, 1] [1, 4])) h)
              · intro q
                fin_cases q
                · exact by
                    intro h
                    exact False.elim ((by decide : ¬ (LexLE [] [4, 1, 1] ∧ LexLE [4, 1, 1] [1, 1, 4])) h)
                · exact by
                    intro h
                    exact False.elim ((by decide : ¬ (LexLE [] [4, 1, 2] ∧ LexLE [4, 1, 2] [2, 1, 4])) h)
                · exact by
                    intro h
                    exact False.elim ((by decide : ¬ (LexLE [] [4, 1, 3] ∧ LexLE [4, 1, 3] [3, 1, 4])) h)
          · exact by
              constructor
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [] [4, 2] ∧ LexLE [4, 2] [2, 4])) h)
              · intro q
                fin_cases q
                · exact by
                    intro h
                    exact False.elim ((by decide : ¬ (LexLE [] [4, 2, 1] ∧ LexLE [4, 2, 1] [1, 2, 4])) h)
                · exact by
                    intro h
                    exact False.elim ((by decide : ¬ (LexLE [] [4, 2, 2] ∧ LexLE [4, 2, 2] [2, 2, 4])) h)
          · exact by
              constructor
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [] [4, 3] ∧ LexLE [4, 3] [3, 4])) h)
              · intro q
                fin_cases q
                · exact by
                    intro h
                    exact False.elim ((by decide : ¬ (LexLE [] [4, 3, 1] ∧ LexLE [4, 3, 1] [1, 3, 4])) h)
          · exact by
              constructor
              · exact by
                  intro _
                  exact k16t8_cover118
              · intro q
                exact Fin.elim0 q
    · exact by
        constructor
        · exact by
            intro _
            exact k16t8_cover119
        · intro q
          fin_cases q
          · exact by
              constructor
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [] [5, 1] ∧ LexLE [5, 1] [1, 5])) h)
              · intro q
                fin_cases q
                · exact by
                    intro h
                    exact False.elim ((by decide : ¬ (LexLE [] [5, 1, 1] ∧ LexLE [5, 1, 1] [1, 1, 5])) h)
                · exact by
                    intro h
                    exact False.elim ((by decide : ¬ (LexLE [] [5, 1, 2] ∧ LexLE [5, 1, 2] [2, 1, 5])) h)
          · exact by
              constructor
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [] [5, 2] ∧ LexLE [5, 2] [2, 5])) h)
              · intro q
                fin_cases q
                · exact by
                    intro h
                    exact False.elim ((by decide : ¬ (LexLE [] [5, 2, 1] ∧ LexLE [5, 2, 1] [1, 2, 5])) h)
          · exact by
              constructor
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [] [5, 3] ∧ LexLE [5, 3] [3, 5])) h)
              · intro q
                exact Fin.elim0 q
    · exact by
        constructor
        · exact by
            intro _
            exact k16t8_cover120
        · intro q
          fin_cases q
          · exact by
              constructor
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [] [6, 1] ∧ LexLE [6, 1] [1, 6])) h)
              · intro q
                fin_cases q
                · exact by
                    intro h
                    exact False.elim ((by decide : ¬ (LexLE [] [6, 1, 1] ∧ LexLE [6, 1, 1] [1, 1, 6])) h)
          · exact by
              constructor
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [] [6, 2] ∧ LexLE [6, 2] [2, 6])) h)
              · intro q
                exact Fin.elim0 q
    · exact by
        constructor
        · exact by
            intro _
            exact k16t8_cover121
        · intro q
          fin_cases q
          · exact by
              constructor
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [] [7, 1] ∧ LexLE [7, 1] [1, 7])) h)
              · intro q
                exact Fin.elim0 q
    · exact by
        constructor
        · exact by
            intro _
            exact k16t8_cover122
        · intro q
          exact Fin.elim0 q

private theorem k16t8_cover9 : ∀ P ∈ pathPatterns 4 8 [], HasCheckedCertificate 16 8 ([[], [], [], []] ++ P) := by
  apply pathPatterns_forall_step
  exact k16t8_seq10


private theorem k16t8_cover126 : ∀ P ∈ pathPatterns 1 6 [1], HasCheckedCertificate 16 8 ([[], [], [], [1], [1]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [1] [] ∧ LexLE [] [])) h)

private theorem k16t8_cover127 : ∀ P ∈ pathPatterns 0 5 [1, 1], HasCheckedCertificate 16 8 ([[], [], [], [1], [1, 1]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k16t8p75, Certificates.k16t8p75_check⟩

private theorem k16t8_cover128 : ∀ P ∈ pathPatterns 0 4 [1, 2], HasCheckedCertificate 16 8 ([[], [], [], [1], [1, 2]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k16t8p76, Certificates.k16t8p76_check⟩

private theorem k16t8_cover129 : ∀ P ∈ pathPatterns 0 3 [1, 3], HasCheckedCertificate 16 8 ([[], [], [], [1], [1, 3]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k16t8p77, Certificates.k16t8p77_check⟩

private theorem k16t8_cover130 : ∀ P ∈ pathPatterns 0 2 [1, 4], HasCheckedCertificate 16 8 ([[], [], [], [1], [1, 4]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k16t8p78, Certificates.k16t8p78_check⟩

private theorem k16t8_cover131 : ∀ P ∈ pathPatterns 0 1 [1, 5], HasCheckedCertificate 16 8 ([[], [], [], [1], [1, 5]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k16t8p79, Certificates.k16t8p79_check⟩

private theorem k16t8_cover132 : ∀ P ∈ pathPatterns 0 0 [1, 6], HasCheckedCertificate 16 8 ([[], [], [], [1], [1, 6]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k16t8p80, Certificates.k16t8p80_check⟩

private theorem k16t8_cover133 : ∀ P ∈ pathPatterns 1 5 [2], HasCheckedCertificate 16 8 ([[], [], [], [1], [2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [2] [] ∧ LexLE [] [])) h)

private theorem k16t8_cover134 : ∀ P ∈ pathPatterns 0 3 [2, 2], HasCheckedCertificate 16 8 ([[], [], [], [1], [2, 2]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k16t8p81, Certificates.k16t8p81_check⟩

private theorem k16t8_cover135 : ∀ P ∈ pathPatterns 0 2 [2, 3], HasCheckedCertificate 16 8 ([[], [], [], [1], [2, 3]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k16t8p82, Certificates.k16t8p82_check⟩

private theorem k16t8_cover136 : ∀ P ∈ pathPatterns 0 1 [2, 4], HasCheckedCertificate 16 8 ([[], [], [], [1], [2, 4]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k16t8p83, Certificates.k16t8p83_check⟩

private theorem k16t8_cover137 : ∀ P ∈ pathPatterns 0 0 [2, 5], HasCheckedCertificate 16 8 ([[], [], [], [1], [2, 5]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k16t8p84, Certificates.k16t8p84_check⟩

private theorem k16t8_cover138 : ∀ P ∈ pathPatterns 1 4 [3], HasCheckedCertificate 16 8 ([[], [], [], [1], [3]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [3] [] ∧ LexLE [] [])) h)

private theorem k16t8_cover139 : ∀ P ∈ pathPatterns 0 1 [3, 3], HasCheckedCertificate 16 8 ([[], [], [], [1], [3, 3]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k16t8p85, Certificates.k16t8p85_check⟩

private theorem k16t8_cover140 : ∀ P ∈ pathPatterns 0 0 [3, 4], HasCheckedCertificate 16 8 ([[], [], [], [1], [3, 4]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k16t8p86, Certificates.k16t8p86_check⟩

private theorem k16t8_cover141 : ∀ P ∈ pathPatterns 1 3 [4], HasCheckedCertificate 16 8 ([[], [], [], [1], [4]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [4] [] ∧ LexLE [] [])) h)

private theorem k16t8_cover142 : ∀ P ∈ pathPatterns 1 2 [5], HasCheckedCertificate 16 8 ([[], [], [], [1], [5]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [5] [] ∧ LexLE [] [])) h)

private theorem k16t8_cover143 : ∀ P ∈ pathPatterns 1 1 [6], HasCheckedCertificate 16 8 ([[], [], [], [1], [6]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [6] [] ∧ LexLE [] [])) h)

private theorem k16t8_cover144 : ∀ P ∈ pathPatterns 1 0 [7], HasCheckedCertificate 16 8 ([[], [], [], [1], [7]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [7] [] ∧ LexLE [] [])) h)

private theorem k16t8_seq125 : amountSequenceForall 2 7 (fun tail =>
    (LexLE [1] ([] ++ tail) ∧ LexLE ([] ++ tail) ([] ++ tail).reverse) →
    ∀ P ∈ pathPatterns (2 - ([] ++ tail).length) (7 - ([] ++ tail).sum) ([] ++ tail),
      HasCheckedCertificate 16 8 ([[], [], [], [1]] ++ (([] ++ tail) :: P))) :=
by
  constructor
  · exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [1] [] ∧ LexLE [] [])) h)
  · intro q
    fin_cases q
    · exact by
        constructor
        · exact by
            intro _
            exact k16t8_cover126
        · intro q
          fin_cases q
          · exact by
              intro _
              exact k16t8_cover127
          · exact by
              intro _
              exact k16t8_cover128
          · exact by
              intro _
              exact k16t8_cover129
          · exact by
              intro _
              exact k16t8_cover130
          · exact by
              intro _
              exact k16t8_cover131
          · exact by
              intro _
              exact k16t8_cover132
    · exact by
        constructor
        · exact by
            intro _
            exact k16t8_cover133
        · intro q
          fin_cases q
          · exact by
              intro h
              exact False.elim ((by decide : ¬ (LexLE [1] [2, 1] ∧ LexLE [2, 1] [1, 2])) h)
          · exact by
              intro _
              exact k16t8_cover134
          · exact by
              intro _
              exact k16t8_cover135
          · exact by
              intro _
              exact k16t8_cover136
          · exact by
              intro _
              exact k16t8_cover137
    · exact by
        constructor
        · exact by
            intro _
            exact k16t8_cover138
        · intro q
          fin_cases q
          · exact by
              intro h
              exact False.elim ((by decide : ¬ (LexLE [1] [3, 1] ∧ LexLE [3, 1] [1, 3])) h)
          · exact by
              intro h
              exact False.elim ((by decide : ¬ (LexLE [1] [3, 2] ∧ LexLE [3, 2] [2, 3])) h)
          · exact by
              intro _
              exact k16t8_cover139
          · exact by
              intro _
              exact k16t8_cover140
    · exact by
        constructor
        · exact by
            intro _
            exact k16t8_cover141
        · intro q
          fin_cases q
          · exact by
              intro h
              exact False.elim ((by decide : ¬ (LexLE [1] [4, 1] ∧ LexLE [4, 1] [1, 4])) h)
          · exact by
              intro h
              exact False.elim ((by decide : ¬ (LexLE [1] [4, 2] ∧ LexLE [4, 2] [2, 4])) h)
          · exact by
              intro h
              exact False.elim ((by decide : ¬ (LexLE [1] [4, 3] ∧ LexLE [4, 3] [3, 4])) h)
    · exact by
        constructor
        · exact by
            intro _
            exact k16t8_cover142
        · intro q
          fin_cases q
          · exact by
              intro h
              exact False.elim ((by decide : ¬ (LexLE [1] [5, 1] ∧ LexLE [5, 1] [1, 5])) h)
          · exact by
              intro h
              exact False.elim ((by decide : ¬ (LexLE [1] [5, 2] ∧ LexLE [5, 2] [2, 5])) h)
    · exact by
        constructor
        · exact by
            intro _
            exact k16t8_cover143
        · intro q
          fin_cases q
          · exact by
              intro h
              exact False.elim ((by decide : ¬ (LexLE [1] [6, 1] ∧ LexLE [6, 1] [1, 6])) h)
    · exact by
        constructor
        · exact by
            intro _
            exact k16t8_cover144
        · intro q
          exact Fin.elim0 q

private theorem k16t8_cover124 : ∀ P ∈ pathPatterns 3 7 [1], HasCheckedCertificate 16 8 ([[], [], [], [1]] ++ P) := by
  apply pathPatterns_forall_step
  exact k16t8_seq125


private theorem k16t8_cover146 : ∀ P ∈ pathPatterns 0 4 [2], HasCheckedCertificate 16 8 ([[], [], [], [1, 1], [2]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k16t8p87, Certificates.k16t8p87_check⟩

private theorem k16t8_cover147 : ∀ P ∈ pathPatterns 0 3 [3], HasCheckedCertificate 16 8 ([[], [], [], [1, 1], [3]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k16t8p88, Certificates.k16t8p88_check⟩

private theorem k16t8_cover148 : ∀ P ∈ pathPatterns 0 2 [4], HasCheckedCertificate 16 8 ([[], [], [], [1, 1], [4]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k16t8p89, Certificates.k16t8p89_check⟩

private theorem k16t8_cover149 : ∀ P ∈ pathPatterns 0 1 [5], HasCheckedCertificate 16 8 ([[], [], [], [1, 1], [5]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k16t8p90, Certificates.k16t8p90_check⟩

private theorem k16t8_cover150 : ∀ P ∈ pathPatterns 0 0 [6], HasCheckedCertificate 16 8 ([[], [], [], [1, 1], [6]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k16t8p91, Certificates.k16t8p91_check⟩

private theorem k16t8_cover145 : ∀ P ∈ pathPatterns 2 6 [1, 1], HasCheckedCertificate 16 8 ([[], [], [], [1, 1]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [1, 1] [] ∧ LexLE [] [])) h)
      · intro q
        fin_cases q
        · exact by
            intro h
            exact False.elim ((by decide : ¬ (LexLE [1, 1] [1] ∧ LexLE [1] [1])) h)
        · exact by
            intro _
            exact k16t8_cover146
        · exact by
            intro _
            exact k16t8_cover147
        · exact by
            intro _
            exact k16t8_cover148
        · exact by
            intro _
            exact k16t8_cover149
        · exact by
            intro _
            exact k16t8_cover150

private theorem k16t8_cover151 : ∀ P ∈ pathPatterns 1 5 [1, 1, 1], HasCheckedCertificate 16 8 ([[], [], [], [1, 1, 1]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [1, 1, 1] [] ∧ LexLE [] [])) h)

private theorem k16t8_cover152 : ∀ P ∈ pathPatterns 0 4 [1, 1, 1, 1], HasCheckedCertificate 16 8 ([[], [], [], [1, 1, 1, 1]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k16t8p92, Certificates.k16t8p92_check⟩

private theorem k16t8_cover153 : ∀ P ∈ pathPatterns 0 3 [1, 1, 1, 2], HasCheckedCertificate 16 8 ([[], [], [], [1, 1, 1, 2]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k16t8p93, Certificates.k16t8p93_check⟩

private theorem k16t8_cover154 : ∀ P ∈ pathPatterns 0 2 [1, 1, 1, 3], HasCheckedCertificate 16 8 ([[], [], [], [1, 1, 1, 3]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k16t8p94, Certificates.k16t8p94_check⟩

private theorem k16t8_cover155 : ∀ P ∈ pathPatterns 0 1 [1, 1, 1, 4], HasCheckedCertificate 16 8 ([[], [], [], [1, 1, 1, 4]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k16t8p95, Certificates.k16t8p95_check⟩

private theorem k16t8_cover156 : ∀ P ∈ pathPatterns 0 0 [1, 1, 1, 5], HasCheckedCertificate 16 8 ([[], [], [], [1, 1, 1, 5]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k16t8p96, Certificates.k16t8p96_check⟩

private theorem k16t8_cover157 : ∀ P ∈ pathPatterns 1 4 [1, 1, 2], HasCheckedCertificate 16 8 ([[], [], [], [1, 1, 2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [1, 1, 2] [] ∧ LexLE [] [])) h)

private theorem k16t8_cover158 : ∀ P ∈ pathPatterns 0 3 [1, 1, 2, 1], HasCheckedCertificate 16 8 ([[], [], [], [1, 1, 2, 1]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k16t8p97, Certificates.k16t8p97_check⟩

private theorem k16t8_cover159 : ∀ P ∈ pathPatterns 0 2 [1, 1, 2, 2], HasCheckedCertificate 16 8 ([[], [], [], [1, 1, 2, 2]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k16t8p98, Certificates.k16t8p98_check⟩

private theorem k16t8_cover160 : ∀ P ∈ pathPatterns 0 1 [1, 1, 2, 3], HasCheckedCertificate 16 8 ([[], [], [], [1, 1, 2, 3]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k16t8p99, Certificates.k16t8p99_check⟩

private theorem k16t8_cover161 : ∀ P ∈ pathPatterns 0 0 [1, 1, 2, 4], HasCheckedCertificate 16 8 ([[], [], [], [1, 1, 2, 4]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k16t8p100, Certificates.k16t8p100_check⟩

private theorem k16t8_cover162 : ∀ P ∈ pathPatterns 1 3 [1, 1, 3], HasCheckedCertificate 16 8 ([[], [], [], [1, 1, 3]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [1, 1, 3] [] ∧ LexLE [] [])) h)

private theorem k16t8_cover163 : ∀ P ∈ pathPatterns 0 2 [1, 1, 3, 1], HasCheckedCertificate 16 8 ([[], [], [], [1, 1, 3, 1]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k16t8p101, Certificates.k16t8p101_check⟩

private theorem k16t8_cover164 : ∀ P ∈ pathPatterns 0 1 [1, 1, 3, 2], HasCheckedCertificate 16 8 ([[], [], [], [1, 1, 3, 2]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k16t8p102, Certificates.k16t8p102_check⟩

private theorem k16t8_cover165 : ∀ P ∈ pathPatterns 0 0 [1, 1, 3, 3], HasCheckedCertificate 16 8 ([[], [], [], [1, 1, 3, 3]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k16t8p103, Certificates.k16t8p103_check⟩

private theorem k16t8_cover166 : ∀ P ∈ pathPatterns 1 2 [1, 1, 4], HasCheckedCertificate 16 8 ([[], [], [], [1, 1, 4]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [1, 1, 4] [] ∧ LexLE [] [])) h)

private theorem k16t8_cover167 : ∀ P ∈ pathPatterns 0 1 [1, 1, 4, 1], HasCheckedCertificate 16 8 ([[], [], [], [1, 1, 4, 1]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k16t8p104, Certificates.k16t8p104_check⟩

private theorem k16t8_cover168 : ∀ P ∈ pathPatterns 0 0 [1, 1, 4, 2], HasCheckedCertificate 16 8 ([[], [], [], [1, 1, 4, 2]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k16t8p105, Certificates.k16t8p105_check⟩

private theorem k16t8_cover169 : ∀ P ∈ pathPatterns 1 1 [1, 1, 5], HasCheckedCertificate 16 8 ([[], [], [], [1, 1, 5]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [1, 1, 5] [] ∧ LexLE [] [])) h)

private theorem k16t8_cover170 : ∀ P ∈ pathPatterns 0 0 [1, 1, 5, 1], HasCheckedCertificate 16 8 ([[], [], [], [1, 1, 5, 1]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k16t8p106, Certificates.k16t8p106_check⟩

private theorem k16t8_cover171 : ∀ P ∈ pathPatterns 1 0 [1, 1, 6], HasCheckedCertificate 16 8 ([[], [], [], [1, 1, 6]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [1, 1, 6] [] ∧ LexLE [] [])) h)

private theorem k16t8_cover173 : ∀ P ∈ pathPatterns 0 3 [2], HasCheckedCertificate 16 8 ([[], [], [], [1, 2], [2]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k16t8p107, Certificates.k16t8p107_check⟩

private theorem k16t8_cover174 : ∀ P ∈ pathPatterns 0 2 [3], HasCheckedCertificate 16 8 ([[], [], [], [1, 2], [3]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k16t8p108, Certificates.k16t8p108_check⟩

private theorem k16t8_cover175 : ∀ P ∈ pathPatterns 0 1 [4], HasCheckedCertificate 16 8 ([[], [], [], [1, 2], [4]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k16t8p109, Certificates.k16t8p109_check⟩

private theorem k16t8_cover176 : ∀ P ∈ pathPatterns 0 0 [5], HasCheckedCertificate 16 8 ([[], [], [], [1, 2], [5]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k16t8p110, Certificates.k16t8p110_check⟩

private theorem k16t8_cover172 : ∀ P ∈ pathPatterns 2 5 [1, 2], HasCheckedCertificate 16 8 ([[], [], [], [1, 2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [1, 2] [] ∧ LexLE [] [])) h)
      · intro q
        fin_cases q
        · exact by
            intro h
            exact False.elim ((by decide : ¬ (LexLE [1, 2] [1] ∧ LexLE [1] [1])) h)
        · exact by
            intro _
            exact k16t8_cover173
        · exact by
            intro _
            exact k16t8_cover174
        · exact by
            intro _
            exact k16t8_cover175
        · exact by
            intro _
            exact k16t8_cover176

private theorem k16t8_cover177 : ∀ P ∈ pathPatterns 1 4 [1, 2, 1], HasCheckedCertificate 16 8 ([[], [], [], [1, 2, 1]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [1, 2, 1] [] ∧ LexLE [] [])) h)

private theorem k16t8_cover178 : ∀ P ∈ pathPatterns 0 2 [1, 2, 1, 2], HasCheckedCertificate 16 8 ([[], [], [], [1, 2, 1, 2]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k16t8p111, Certificates.k16t8p111_check⟩

private theorem k16t8_cover179 : ∀ P ∈ pathPatterns 0 1 [1, 2, 1, 3], HasCheckedCertificate 16 8 ([[], [], [], [1, 2, 1, 3]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k16t8p112, Certificates.k16t8p112_check⟩

private theorem k16t8_cover180 : ∀ P ∈ pathPatterns 0 0 [1, 2, 1, 4], HasCheckedCertificate 16 8 ([[], [], [], [1, 2, 1, 4]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k16t8p113, Certificates.k16t8p113_check⟩

private theorem k16t8_cover181 : ∀ P ∈ pathPatterns 1 3 [1, 2, 2], HasCheckedCertificate 16 8 ([[], [], [], [1, 2, 2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [1, 2, 2] [] ∧ LexLE [] [])) h)

private theorem k16t8_cover182 : ∀ P ∈ pathPatterns 0 2 [1, 2, 2, 1], HasCheckedCertificate 16 8 ([[], [], [], [1, 2, 2, 1]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k16t8p114, Certificates.k16t8p114_check⟩

private theorem k16t8_cover183 : ∀ P ∈ pathPatterns 0 1 [1, 2, 2, 2], HasCheckedCertificate 16 8 ([[], [], [], [1, 2, 2, 2]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k16t8p115, Certificates.k16t8p115_check⟩

private theorem k16t8_cover184 : ∀ P ∈ pathPatterns 0 0 [1, 2, 2, 3], HasCheckedCertificate 16 8 ([[], [], [], [1, 2, 2, 3]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k16t8p116, Certificates.k16t8p116_check⟩

private theorem k16t8_cover185 : ∀ P ∈ pathPatterns 1 2 [1, 2, 3], HasCheckedCertificate 16 8 ([[], [], [], [1, 2, 3]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [1, 2, 3] [] ∧ LexLE [] [])) h)

private theorem k16t8_cover186 : ∀ P ∈ pathPatterns 0 1 [1, 2, 3, 1], HasCheckedCertificate 16 8 ([[], [], [], [1, 2, 3, 1]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k16t8p117, Certificates.k16t8p117_check⟩

private theorem k16t8_cover187 : ∀ P ∈ pathPatterns 0 0 [1, 2, 3, 2], HasCheckedCertificate 16 8 ([[], [], [], [1, 2, 3, 2]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k16t8p118, Certificates.k16t8p118_check⟩

private theorem k16t8_cover188 : ∀ P ∈ pathPatterns 1 1 [1, 2, 4], HasCheckedCertificate 16 8 ([[], [], [], [1, 2, 4]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [1, 2, 4] [] ∧ LexLE [] [])) h)

private theorem k16t8_cover189 : ∀ P ∈ pathPatterns 0 0 [1, 2, 4, 1], HasCheckedCertificate 16 8 ([[], [], [], [1, 2, 4, 1]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k16t8p119, Certificates.k16t8p119_check⟩

private theorem k16t8_cover190 : ∀ P ∈ pathPatterns 1 0 [1, 2, 5], HasCheckedCertificate 16 8 ([[], [], [], [1, 2, 5]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [1, 2, 5] [] ∧ LexLE [] [])) h)

private theorem k16t8_cover192 : ∀ P ∈ pathPatterns 0 2 [2], HasCheckedCertificate 16 8 ([[], [], [], [1, 3], [2]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k16t8p120, Certificates.k16t8p120_check⟩

private theorem k16t8_cover193 : ∀ P ∈ pathPatterns 0 1 [3], HasCheckedCertificate 16 8 ([[], [], [], [1, 3], [3]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k16t8p121, Certificates.k16t8p121_check⟩

private theorem k16t8_cover194 : ∀ P ∈ pathPatterns 0 0 [4], HasCheckedCertificate 16 8 ([[], [], [], [1, 3], [4]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k16t8p122, Certificates.k16t8p122_check⟩

private theorem k16t8_cover191 : ∀ P ∈ pathPatterns 2 4 [1, 3], HasCheckedCertificate 16 8 ([[], [], [], [1, 3]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [1, 3] [] ∧ LexLE [] [])) h)
      · intro q
        fin_cases q
        · exact by
            intro h
            exact False.elim ((by decide : ¬ (LexLE [1, 3] [1] ∧ LexLE [1] [1])) h)
        · exact by
            intro _
            exact k16t8_cover192
        · exact by
            intro _
            exact k16t8_cover193
        · exact by
            intro _
            exact k16t8_cover194

private theorem k16t8_cover195 : ∀ P ∈ pathPatterns 1 3 [1, 3, 1], HasCheckedCertificate 16 8 ([[], [], [], [1, 3, 1]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [1, 3, 1] [] ∧ LexLE [] [])) h)

private theorem k16t8_cover196 : ∀ P ∈ pathPatterns 0 1 [1, 3, 1, 2], HasCheckedCertificate 16 8 ([[], [], [], [1, 3, 1, 2]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k16t8p123, Certificates.k16t8p123_check⟩

private theorem k16t8_cover197 : ∀ P ∈ pathPatterns 0 0 [1, 3, 1, 3], HasCheckedCertificate 16 8 ([[], [], [], [1, 3, 1, 3]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k16t8p124, Certificates.k16t8p124_check⟩

private theorem k16t8_cover198 : ∀ P ∈ pathPatterns 1 2 [1, 3, 2], HasCheckedCertificate 16 8 ([[], [], [], [1, 3, 2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [1, 3, 2] [] ∧ LexLE [] [])) h)

private theorem k16t8_cover199 : ∀ P ∈ pathPatterns 0 0 [1, 3, 2, 2], HasCheckedCertificate 16 8 ([[], [], [], [1, 3, 2, 2]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k16t8p125, Certificates.k16t8p125_check⟩

private theorem k16t8_cover200 : ∀ P ∈ pathPatterns 1 1 [1, 3, 3], HasCheckedCertificate 16 8 ([[], [], [], [1, 3, 3]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [1, 3, 3] [] ∧ LexLE [] [])) h)

private theorem k16t8_cover201 : ∀ P ∈ pathPatterns 0 0 [1, 3, 3, 1], HasCheckedCertificate 16 8 ([[], [], [], [1, 3, 3, 1]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k16t8p126, Certificates.k16t8p126_check⟩

private theorem k16t8_cover202 : ∀ P ∈ pathPatterns 1 0 [1, 3, 4], HasCheckedCertificate 16 8 ([[], [], [], [1, 3, 4]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [1, 3, 4] [] ∧ LexLE [] [])) h)

private theorem k16t8_cover204 : ∀ P ∈ pathPatterns 0 1 [2], HasCheckedCertificate 16 8 ([[], [], [], [1, 4], [2]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k16t8p127, Certificates.k16t8p127_check⟩

private theorem k16t8_cover205 : ∀ P ∈ pathPatterns 0 0 [3], HasCheckedCertificate 16 8 ([[], [], [], [1, 4], [3]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k16t8p128, Certificates.k16t8p128_check⟩

private theorem k16t8_cover203 : ∀ P ∈ pathPatterns 2 3 [1, 4], HasCheckedCertificate 16 8 ([[], [], [], [1, 4]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [1, 4] [] ∧ LexLE [] [])) h)
      · intro q
        fin_cases q
        · exact by
            intro h
            exact False.elim ((by decide : ¬ (LexLE [1, 4] [1] ∧ LexLE [1] [1])) h)
        · exact by
            intro _
            exact k16t8_cover204
        · exact by
            intro _
            exact k16t8_cover205

private theorem k16t8_cover206 : ∀ P ∈ pathPatterns 1 2 [1, 4, 1], HasCheckedCertificate 16 8 ([[], [], [], [1, 4, 1]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [1, 4, 1] [] ∧ LexLE [] [])) h)

private theorem k16t8_cover207 : ∀ P ∈ pathPatterns 0 0 [1, 4, 1, 2], HasCheckedCertificate 16 8 ([[], [], [], [1, 4, 1, 2]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k16t8p129, Certificates.k16t8p129_check⟩

private theorem k16t8_cover208 : ∀ P ∈ pathPatterns 1 1 [1, 4, 2], HasCheckedCertificate 16 8 ([[], [], [], [1, 4, 2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [1, 4, 2] [] ∧ LexLE [] [])) h)

private theorem k16t8_cover209 : ∀ P ∈ pathPatterns 1 0 [1, 4, 3], HasCheckedCertificate 16 8 ([[], [], [], [1, 4, 3]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [1, 4, 3] [] ∧ LexLE [] [])) h)

private theorem k16t8_cover211 : ∀ P ∈ pathPatterns 0 0 [2], HasCheckedCertificate 16 8 ([[], [], [], [1, 5], [2]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k16t8p130, Certificates.k16t8p130_check⟩

private theorem k16t8_cover210 : ∀ P ∈ pathPatterns 2 2 [1, 5], HasCheckedCertificate 16 8 ([[], [], [], [1, 5]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [1, 5] [] ∧ LexLE [] [])) h)
      · intro q
        fin_cases q
        · exact by
            intro h
            exact False.elim ((by decide : ¬ (LexLE [1, 5] [1] ∧ LexLE [1] [1])) h)
        · exact by
            intro _
            exact k16t8_cover211

private theorem k16t8_cover212 : ∀ P ∈ pathPatterns 1 1 [1, 5, 1], HasCheckedCertificate 16 8 ([[], [], [], [1, 5, 1]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [1, 5, 1] [] ∧ LexLE [] [])) h)

private theorem k16t8_cover213 : ∀ P ∈ pathPatterns 1 0 [1, 5, 2], HasCheckedCertificate 16 8 ([[], [], [], [1, 5, 2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [1, 5, 2] [] ∧ LexLE [] [])) h)

private theorem k16t8_cover214 : ∀ P ∈ pathPatterns 2 1 [1, 6], HasCheckedCertificate 16 8 ([[], [], [], [1, 6]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [1, 6] [] ∧ LexLE [] [])) h)
      · intro q
        fin_cases q
        · exact by
            intro h
            exact False.elim ((by decide : ¬ (LexLE [1, 6] [1] ∧ LexLE [1] [1])) h)

private theorem k16t8_cover215 : ∀ P ∈ pathPatterns 1 0 [1, 6, 1], HasCheckedCertificate 16 8 ([[], [], [], [1, 6, 1]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [1, 6, 1] [] ∧ LexLE [] [])) h)

private theorem k16t8_cover216 : ∀ P ∈ pathPatterns 2 0 [1, 7], HasCheckedCertificate 16 8 ([[], [], [], [1, 7]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [1, 7] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k16t8_seq123 : amountSequenceForall 3 7 (fun tail =>
    (LexLE [] ([1] ++ tail) ∧ LexLE ([1] ++ tail) ([1] ++ tail).reverse) →
    ∀ P ∈ pathPatterns (4 - ([1] ++ tail).length) (8 - ([1] ++ tail).sum) ([1] ++ tail),
      HasCheckedCertificate 16 8 ([[], [], []] ++ (([1] ++ tail) :: P))) :=
by
  constructor
  · exact by
      intro _
      exact k16t8_cover124
  · intro q
    fin_cases q
    · exact by
        constructor
        · exact by
            intro _
            exact k16t8_cover145
        · intro q
          fin_cases q
          · exact by
              constructor
              · exact by
                  intro _
                  exact k16t8_cover151
              · intro q
                fin_cases q
                · exact by
                    intro _
                    exact k16t8_cover152
                · exact by
                    intro _
                    exact k16t8_cover153
                · exact by
                    intro _
                    exact k16t8_cover154
                · exact by
                    intro _
                    exact k16t8_cover155
                · exact by
                    intro _
                    exact k16t8_cover156
          · exact by
              constructor
              · exact by
                  intro _
                  exact k16t8_cover157
              · intro q
                fin_cases q
                · exact by
                    intro _
                    exact k16t8_cover158
                · exact by
                    intro _
                    exact k16t8_cover159
                · exact by
                    intro _
                    exact k16t8_cover160
                · exact by
                    intro _
                    exact k16t8_cover161
          · exact by
              constructor
              · exact by
                  intro _
                  exact k16t8_cover162
              · intro q
                fin_cases q
                · exact by
                    intro _
                    exact k16t8_cover163
                · exact by
                    intro _
                    exact k16t8_cover164
                · exact by
                    intro _
                    exact k16t8_cover165
          · exact by
              constructor
              · exact by
                  intro _
                  exact k16t8_cover166
              · intro q
                fin_cases q
                · exact by
                    intro _
                    exact k16t8_cover167
                · exact by
                    intro _
                    exact k16t8_cover168
          · exact by
              constructor
              · exact by
                  intro _
                  exact k16t8_cover169
              · intro q
                fin_cases q
                · exact by
                    intro _
                    exact k16t8_cover170
          · exact by
              constructor
              · exact by
                  intro _
                  exact k16t8_cover171
              · intro q
                exact Fin.elim0 q
    · exact by
        constructor
        · exact by
            intro _
            exact k16t8_cover172
        · intro q
          fin_cases q
          · exact by
              constructor
              · exact by
                  intro _
                  exact k16t8_cover177
              · intro q
                fin_cases q
                · exact by
                    intro h
                    exact False.elim ((by decide : ¬ (LexLE [] [1, 2, 1, 1] ∧ LexLE [1, 2, 1, 1] [1, 1, 2, 1])) h)
                · exact by
                    intro _
                    exact k16t8_cover178
                · exact by
                    intro _
                    exact k16t8_cover179
                · exact by
                    intro _
                    exact k16t8_cover180
          · exact by
              constructor
              · exact by
                  intro _
                  exact k16t8_cover181
              · intro q
                fin_cases q
                · exact by
                    intro _
                    exact k16t8_cover182
                · exact by
                    intro _
                    exact k16t8_cover183
                · exact by
                    intro _
                    exact k16t8_cover184
          · exact by
              constructor
              · exact by
                  intro _
                  exact k16t8_cover185
              · intro q
                fin_cases q
                · exact by
                    intro _
                    exact k16t8_cover186
                · exact by
                    intro _
                    exact k16t8_cover187
          · exact by
              constructor
              · exact by
                  intro _
                  exact k16t8_cover188
              · intro q
                fin_cases q
                · exact by
                    intro _
                    exact k16t8_cover189
          · exact by
              constructor
              · exact by
                  intro _
                  exact k16t8_cover190
              · intro q
                exact Fin.elim0 q
    · exact by
        constructor
        · exact by
            intro _
            exact k16t8_cover191
        · intro q
          fin_cases q
          · exact by
              constructor
              · exact by
                  intro _
                  exact k16t8_cover195
              · intro q
                fin_cases q
                · exact by
                    intro h
                    exact False.elim ((by decide : ¬ (LexLE [] [1, 3, 1, 1] ∧ LexLE [1, 3, 1, 1] [1, 1, 3, 1])) h)
                · exact by
                    intro _
                    exact k16t8_cover196
                · exact by
                    intro _
                    exact k16t8_cover197
          · exact by
              constructor
              · exact by
                  intro _
                  exact k16t8_cover198
              · intro q
                fin_cases q
                · exact by
                    intro h
                    exact False.elim ((by decide : ¬ (LexLE [] [1, 3, 2, 1] ∧ LexLE [1, 3, 2, 1] [1, 2, 3, 1])) h)
                · exact by
                    intro _
                    exact k16t8_cover199
          · exact by
              constructor
              · exact by
                  intro _
                  exact k16t8_cover200
              · intro q
                fin_cases q
                · exact by
                    intro _
                    exact k16t8_cover201
          · exact by
              constructor
              · exact by
                  intro _
                  exact k16t8_cover202
              · intro q
                exact Fin.elim0 q
    · exact by
        constructor
        · exact by
            intro _
            exact k16t8_cover203
        · intro q
          fin_cases q
          · exact by
              constructor
              · exact by
                  intro _
                  exact k16t8_cover206
              · intro q
                fin_cases q
                · exact by
                    intro h
                    exact False.elim ((by decide : ¬ (LexLE [] [1, 4, 1, 1] ∧ LexLE [1, 4, 1, 1] [1, 1, 4, 1])) h)
                · exact by
                    intro _
                    exact k16t8_cover207
          · exact by
              constructor
              · exact by
                  intro _
                  exact k16t8_cover208
              · intro q
                fin_cases q
                · exact by
                    intro h
                    exact False.elim ((by decide : ¬ (LexLE [] [1, 4, 2, 1] ∧ LexLE [1, 4, 2, 1] [1, 2, 4, 1])) h)
          · exact by
              constructor
              · exact by
                  intro _
                  exact k16t8_cover209
              · intro q
                exact Fin.elim0 q
    · exact by
        constructor
        · exact by
            intro _
            exact k16t8_cover210
        · intro q
          fin_cases q
          · exact by
              constructor
              · exact by
                  intro _
                  exact k16t8_cover212
              · intro q
                fin_cases q
                · exact by
                    intro h
                    exact False.elim ((by decide : ¬ (LexLE [] [1, 5, 1, 1] ∧ LexLE [1, 5, 1, 1] [1, 1, 5, 1])) h)
          · exact by
              constructor
              · exact by
                  intro _
                  exact k16t8_cover213
              · intro q
                exact Fin.elim0 q
    · exact by
        constructor
        · exact by
            intro _
            exact k16t8_cover214
        · intro q
          fin_cases q
          · exact by
              constructor
              · exact by
                  intro _
                  exact k16t8_cover215
              · intro q
                exact Fin.elim0 q
    · exact by
        constructor
        · exact by
            intro _
            exact k16t8_cover216
        · intro q
          exact Fin.elim0 q

private theorem k16t8_cover219 : ∀ P ∈ pathPatterns 1 4 [2], HasCheckedCertificate 16 8 ([[], [], [], [2], [2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [2] [] ∧ LexLE [] [])) h)

private theorem k16t8_cover220 : ∀ P ∈ pathPatterns 0 2 [2, 2], HasCheckedCertificate 16 8 ([[], [], [], [2], [2, 2]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k16t8p131, Certificates.k16t8p131_check⟩

private theorem k16t8_cover221 : ∀ P ∈ pathPatterns 0 1 [2, 3], HasCheckedCertificate 16 8 ([[], [], [], [2], [2, 3]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k16t8p132, Certificates.k16t8p132_check⟩

private theorem k16t8_cover222 : ∀ P ∈ pathPatterns 0 0 [2, 4], HasCheckedCertificate 16 8 ([[], [], [], [2], [2, 4]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k16t8p133, Certificates.k16t8p133_check⟩

private theorem k16t8_cover223 : ∀ P ∈ pathPatterns 1 3 [3], HasCheckedCertificate 16 8 ([[], [], [], [2], [3]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [3] [] ∧ LexLE [] [])) h)

private theorem k16t8_cover224 : ∀ P ∈ pathPatterns 0 0 [3, 3], HasCheckedCertificate 16 8 ([[], [], [], [2], [3, 3]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k16t8p134, Certificates.k16t8p134_check⟩

private theorem k16t8_cover225 : ∀ P ∈ pathPatterns 1 2 [4], HasCheckedCertificate 16 8 ([[], [], [], [2], [4]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [4] [] ∧ LexLE [] [])) h)

private theorem k16t8_cover226 : ∀ P ∈ pathPatterns 1 1 [5], HasCheckedCertificate 16 8 ([[], [], [], [2], [5]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [5] [] ∧ LexLE [] [])) h)

private theorem k16t8_cover227 : ∀ P ∈ pathPatterns 1 0 [6], HasCheckedCertificate 16 8 ([[], [], [], [2], [6]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [6] [] ∧ LexLE [] [])) h)

private theorem k16t8_cover218 : ∀ P ∈ pathPatterns 3 6 [2], HasCheckedCertificate 16 8 ([[], [], [], [2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [2] [] ∧ LexLE [] [])) h)
      · intro q
        fin_cases q
        · exact by
            constructor
            · exact by
                intro h
                exact False.elim ((by decide : ¬ (LexLE [2] [1] ∧ LexLE [1] [1])) h)
            · intro q
              fin_cases q
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [2] [1, 1] ∧ LexLE [1, 1] [1, 1])) h)
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [2] [1, 2] ∧ LexLE [1, 2] [2, 1])) h)
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [2] [1, 3] ∧ LexLE [1, 3] [3, 1])) h)
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [2] [1, 4] ∧ LexLE [1, 4] [4, 1])) h)
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [2] [1, 5] ∧ LexLE [1, 5] [5, 1])) h)
        · exact by
            constructor
            · exact by
                intro _
                exact k16t8_cover219
            · intro q
              fin_cases q
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [2] [2, 1] ∧ LexLE [2, 1] [1, 2])) h)
              · exact by
                  intro _
                  exact k16t8_cover220
              · exact by
                  intro _
                  exact k16t8_cover221
              · exact by
                  intro _
                  exact k16t8_cover222
        · exact by
            constructor
            · exact by
                intro _
                exact k16t8_cover223
            · intro q
              fin_cases q
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [2] [3, 1] ∧ LexLE [3, 1] [1, 3])) h)
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [2] [3, 2] ∧ LexLE [3, 2] [2, 3])) h)
              · exact by
                  intro _
                  exact k16t8_cover224
        · exact by
            constructor
            · exact by
                intro _
                exact k16t8_cover225
            · intro q
              fin_cases q
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [2] [4, 1] ∧ LexLE [4, 1] [1, 4])) h)
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [2] [4, 2] ∧ LexLE [4, 2] [2, 4])) h)
        · exact by
            constructor
            · exact by
                intro _
                exact k16t8_cover226
            · intro q
              fin_cases q
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [2] [5, 1] ∧ LexLE [5, 1] [1, 5])) h)
        · exact by
            constructor
            · exact by
                intro _
                exact k16t8_cover227
            · intro q
              exact Fin.elim0 q

private theorem k16t8_cover228 : ∀ P ∈ pathPatterns 0 2 [2, 1, 1, 2], HasCheckedCertificate 16 8 ([[], [], [], [2, 1, 1, 2]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k16t8p135, Certificates.k16t8p135_check⟩

private theorem k16t8_cover229 : ∀ P ∈ pathPatterns 0 1 [2, 1, 1, 3], HasCheckedCertificate 16 8 ([[], [], [], [2, 1, 1, 3]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k16t8p136, Certificates.k16t8p136_check⟩

private theorem k16t8_cover230 : ∀ P ∈ pathPatterns 0 0 [2, 1, 1, 4], HasCheckedCertificate 16 8 ([[], [], [], [2, 1, 1, 4]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k16t8p137, Certificates.k16t8p137_check⟩

private theorem k16t8_cover231 : ∀ P ∈ pathPatterns 1 3 [2, 1, 2], HasCheckedCertificate 16 8 ([[], [], [], [2, 1, 2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [2, 1, 2] [] ∧ LexLE [] [])) h)

private theorem k16t8_cover232 : ∀ P ∈ pathPatterns 0 1 [2, 1, 2, 2], HasCheckedCertificate 16 8 ([[], [], [], [2, 1, 2, 2]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k16t8p138, Certificates.k16t8p138_check⟩

private theorem k16t8_cover233 : ∀ P ∈ pathPatterns 0 0 [2, 1, 2, 3], HasCheckedCertificate 16 8 ([[], [], [], [2, 1, 2, 3]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k16t8p139, Certificates.k16t8p139_check⟩

private theorem k16t8_cover234 : ∀ P ∈ pathPatterns 1 2 [2, 1, 3], HasCheckedCertificate 16 8 ([[], [], [], [2, 1, 3]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [2, 1, 3] [] ∧ LexLE [] [])) h)

private theorem k16t8_cover235 : ∀ P ∈ pathPatterns 0 0 [2, 1, 3, 2], HasCheckedCertificate 16 8 ([[], [], [], [2, 1, 3, 2]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k16t8p140, Certificates.k16t8p140_check⟩

private theorem k16t8_cover236 : ∀ P ∈ pathPatterns 1 1 [2, 1, 4], HasCheckedCertificate 16 8 ([[], [], [], [2, 1, 4]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [2, 1, 4] [] ∧ LexLE [] [])) h)

private theorem k16t8_cover237 : ∀ P ∈ pathPatterns 1 0 [2, 1, 5], HasCheckedCertificate 16 8 ([[], [], [], [2, 1, 5]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [2, 1, 5] [] ∧ LexLE [] [])) h)

private theorem k16t8_cover239 : ∀ P ∈ pathPatterns 0 1 [3], HasCheckedCertificate 16 8 ([[], [], [], [2, 2], [3]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k16t8p141, Certificates.k16t8p141_check⟩

private theorem k16t8_cover240 : ∀ P ∈ pathPatterns 0 0 [4], HasCheckedCertificate 16 8 ([[], [], [], [2, 2], [4]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k16t8p142, Certificates.k16t8p142_check⟩

private theorem k16t8_cover238 : ∀ P ∈ pathPatterns 2 4 [2, 2], HasCheckedCertificate 16 8 ([[], [], [], [2, 2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [2, 2] [] ∧ LexLE [] [])) h)
      · intro q
        fin_cases q
        · exact by
            intro h
            exact False.elim ((by decide : ¬ (LexLE [2, 2] [1] ∧ LexLE [1] [1])) h)
        · exact by
            intro h
            exact False.elim ((by decide : ¬ (LexLE [2, 2] [2] ∧ LexLE [2] [2])) h)
        · exact by
            intro _
            exact k16t8_cover239
        · exact by
            intro _
            exact k16t8_cover240

private theorem k16t8_cover241 : ∀ P ∈ pathPatterns 0 0 [2, 2, 1, 3], HasCheckedCertificate 16 8 ([[], [], [], [2, 2, 1, 3]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k16t8p143, Certificates.k16t8p143_check⟩

private theorem k16t8_cover242 : ∀ P ∈ pathPatterns 1 2 [2, 2, 2], HasCheckedCertificate 16 8 ([[], [], [], [2, 2, 2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [2, 2, 2] [] ∧ LexLE [] [])) h)

private theorem k16t8_cover243 : ∀ P ∈ pathPatterns 0 0 [2, 2, 2, 2], HasCheckedCertificate 16 8 ([[], [], [], [2, 2, 2, 2]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k16t8p144, Certificates.k16t8p144_check⟩

private theorem k16t8_cover244 : ∀ P ∈ pathPatterns 1 1 [2, 2, 3], HasCheckedCertificate 16 8 ([[], [], [], [2, 2, 3]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [2, 2, 3] [] ∧ LexLE [] [])) h)

private theorem k16t8_cover245 : ∀ P ∈ pathPatterns 1 0 [2, 2, 4], HasCheckedCertificate 16 8 ([[], [], [], [2, 2, 4]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [2, 2, 4] [] ∧ LexLE [] [])) h)

private theorem k16t8_cover247 : ∀ P ∈ pathPatterns 0 0 [3], HasCheckedCertificate 16 8 ([[], [], [], [2, 3], [3]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k16t8p145, Certificates.k16t8p145_check⟩

private theorem k16t8_cover246 : ∀ P ∈ pathPatterns 2 3 [2, 3], HasCheckedCertificate 16 8 ([[], [], [], [2, 3]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [2, 3] [] ∧ LexLE [] [])) h)
      · intro q
        fin_cases q
        · exact by
            intro h
            exact False.elim ((by decide : ¬ (LexLE [2, 3] [1] ∧ LexLE [1] [1])) h)
        · exact by
            intro h
            exact False.elim ((by decide : ¬ (LexLE [2, 3] [2] ∧ LexLE [2] [2])) h)
        · exact by
            intro _
            exact k16t8_cover247

private theorem k16t8_cover248 : ∀ P ∈ pathPatterns 1 1 [2, 3, 2], HasCheckedCertificate 16 8 ([[], [], [], [2, 3, 2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [2, 3, 2] [] ∧ LexLE [] [])) h)

private theorem k16t8_cover249 : ∀ P ∈ pathPatterns 1 0 [2, 3, 3], HasCheckedCertificate 16 8 ([[], [], [], [2, 3, 3]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [2, 3, 3] [] ∧ LexLE [] [])) h)

private theorem k16t8_cover250 : ∀ P ∈ pathPatterns 2 2 [2, 4], HasCheckedCertificate 16 8 ([[], [], [], [2, 4]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [2, 4] [] ∧ LexLE [] [])) h)
      · intro q
        fin_cases q
        · exact by
            intro h
            exact False.elim ((by decide : ¬ (LexLE [2, 4] [1] ∧ LexLE [1] [1])) h)
        · exact by
            intro h
            exact False.elim ((by decide : ¬ (LexLE [2, 4] [2] ∧ LexLE [2] [2])) h)

private theorem k16t8_cover251 : ∀ P ∈ pathPatterns 1 0 [2, 4, 2], HasCheckedCertificate 16 8 ([[], [], [], [2, 4, 2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [2, 4, 2] [] ∧ LexLE [] [])) h)

private theorem k16t8_cover252 : ∀ P ∈ pathPatterns 2 1 [2, 5], HasCheckedCertificate 16 8 ([[], [], [], [2, 5]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [2, 5] [] ∧ LexLE [] [])) h)
      · intro q
        fin_cases q
        · exact by
            intro h
            exact False.elim ((by decide : ¬ (LexLE [2, 5] [1] ∧ LexLE [1] [1])) h)

private theorem k16t8_cover253 : ∀ P ∈ pathPatterns 2 0 [2, 6], HasCheckedCertificate 16 8 ([[], [], [], [2, 6]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [2, 6] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k16t8_seq217 : amountSequenceForall 3 6 (fun tail =>
    (LexLE [] ([2] ++ tail) ∧ LexLE ([2] ++ tail) ([2] ++ tail).reverse) →
    ∀ P ∈ pathPatterns (4 - ([2] ++ tail).length) (8 - ([2] ++ tail).sum) ([2] ++ tail),
      HasCheckedCertificate 16 8 ([[], [], []] ++ (([2] ++ tail) :: P))) :=
by
  constructor
  · exact by
      intro _
      exact k16t8_cover218
  · intro q
    fin_cases q
    · exact by
        constructor
        · exact by
            intro h
            exact False.elim ((by decide : ¬ (LexLE [] [2, 1] ∧ LexLE [2, 1] [1, 2])) h)
        · intro q
          fin_cases q
          · exact by
              constructor
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [] [2, 1, 1] ∧ LexLE [2, 1, 1] [1, 1, 2])) h)
              · intro q
                fin_cases q
                · exact by
                    intro h
                    exact False.elim ((by decide : ¬ (LexLE [] [2, 1, 1, 1] ∧ LexLE [2, 1, 1, 1] [1, 1, 1, 2])) h)
                · exact by
                    intro _
                    exact k16t8_cover228
                · exact by
                    intro _
                    exact k16t8_cover229
                · exact by
                    intro _
                    exact k16t8_cover230
          · exact by
              constructor
              · exact by
                  intro _
                  exact k16t8_cover231
              · intro q
                fin_cases q
                · exact by
                    intro h
                    exact False.elim ((by decide : ¬ (LexLE [] [2, 1, 2, 1] ∧ LexLE [2, 1, 2, 1] [1, 2, 1, 2])) h)
                · exact by
                    intro _
                    exact k16t8_cover232
                · exact by
                    intro _
                    exact k16t8_cover233
          · exact by
              constructor
              · exact by
                  intro _
                  exact k16t8_cover234
              · intro q
                fin_cases q
                · exact by
                    intro h
                    exact False.elim ((by decide : ¬ (LexLE [] [2, 1, 3, 1] ∧ LexLE [2, 1, 3, 1] [1, 3, 1, 2])) h)
                · exact by
                    intro _
                    exact k16t8_cover235
          · exact by
              constructor
              · exact by
                  intro _
                  exact k16t8_cover236
              · intro q
                fin_cases q
                · exact by
                    intro h
                    exact False.elim ((by decide : ¬ (LexLE [] [2, 1, 4, 1] ∧ LexLE [2, 1, 4, 1] [1, 4, 1, 2])) h)
          · exact by
              constructor
              · exact by
                  intro _
                  exact k16t8_cover237
              · intro q
                exact Fin.elim0 q
    · exact by
        constructor
        · exact by
            intro _
            exact k16t8_cover238
        · intro q
          fin_cases q
          · exact by
              constructor
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [] [2, 2, 1] ∧ LexLE [2, 2, 1] [1, 2, 2])) h)
              · intro q
                fin_cases q
                · exact by
                    intro h
                    exact False.elim ((by decide : ¬ (LexLE [] [2, 2, 1, 1] ∧ LexLE [2, 2, 1, 1] [1, 1, 2, 2])) h)
                · exact by
                    intro h
                    exact False.elim ((by decide : ¬ (LexLE [] [2, 2, 1, 2] ∧ LexLE [2, 2, 1, 2] [2, 1, 2, 2])) h)
                · exact by
                    intro _
                    exact k16t8_cover241
          · exact by
              constructor
              · exact by
                  intro _
                  exact k16t8_cover242
              · intro q
                fin_cases q
                · exact by
                    intro h
                    exact False.elim ((by decide : ¬ (LexLE [] [2, 2, 2, 1] ∧ LexLE [2, 2, 2, 1] [1, 2, 2, 2])) h)
                · exact by
                    intro _
                    exact k16t8_cover243
          · exact by
              constructor
              · exact by
                  intro _
                  exact k16t8_cover244
              · intro q
                fin_cases q
                · exact by
                    intro h
                    exact False.elim ((by decide : ¬ (LexLE [] [2, 2, 3, 1] ∧ LexLE [2, 2, 3, 1] [1, 3, 2, 2])) h)
          · exact by
              constructor
              · exact by
                  intro _
                  exact k16t8_cover245
              · intro q
                exact Fin.elim0 q
    · exact by
        constructor
        · exact by
            intro _
            exact k16t8_cover246
        · intro q
          fin_cases q
          · exact by
              constructor
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [] [2, 3, 1] ∧ LexLE [2, 3, 1] [1, 3, 2])) h)
              · intro q
                fin_cases q
                · exact by
                    intro h
                    exact False.elim ((by decide : ¬ (LexLE [] [2, 3, 1, 1] ∧ LexLE [2, 3, 1, 1] [1, 1, 3, 2])) h)
                · exact by
                    intro h
                    exact False.elim ((by decide : ¬ (LexLE [] [2, 3, 1, 2] ∧ LexLE [2, 3, 1, 2] [2, 1, 3, 2])) h)
          · exact by
              constructor
              · exact by
                  intro _
                  exact k16t8_cover248
              · intro q
                fin_cases q
                · exact by
                    intro h
                    exact False.elim ((by decide : ¬ (LexLE [] [2, 3, 2, 1] ∧ LexLE [2, 3, 2, 1] [1, 2, 3, 2])) h)
          · exact by
              constructor
              · exact by
                  intro _
                  exact k16t8_cover249
              · intro q
                exact Fin.elim0 q
    · exact by
        constructor
        · exact by
            intro _
            exact k16t8_cover250
        · intro q
          fin_cases q
          · exact by
              constructor
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [] [2, 4, 1] ∧ LexLE [2, 4, 1] [1, 4, 2])) h)
              · intro q
                fin_cases q
                · exact by
                    intro h
                    exact False.elim ((by decide : ¬ (LexLE [] [2, 4, 1, 1] ∧ LexLE [2, 4, 1, 1] [1, 1, 4, 2])) h)
          · exact by
              constructor
              · exact by
                  intro _
                  exact k16t8_cover251
              · intro q
                exact Fin.elim0 q
    · exact by
        constructor
        · exact by
            intro _
            exact k16t8_cover252
        · intro q
          fin_cases q
          · exact by
              constructor
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [] [2, 5, 1] ∧ LexLE [2, 5, 1] [1, 5, 2])) h)
              · intro q
                exact Fin.elim0 q
    · exact by
        constructor
        · exact by
            intro _
            exact k16t8_cover253
        · intro q
          exact Fin.elim0 q

private theorem k16t8_cover256 : ∀ P ∈ pathPatterns 1 2 [3], HasCheckedCertificate 16 8 ([[], [], [], [3], [3]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [3] [] ∧ LexLE [] [])) h)

private theorem k16t8_cover257 : ∀ P ∈ pathPatterns 1 1 [4], HasCheckedCertificate 16 8 ([[], [], [], [3], [4]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [4] [] ∧ LexLE [] [])) h)

private theorem k16t8_cover258 : ∀ P ∈ pathPatterns 1 0 [5], HasCheckedCertificate 16 8 ([[], [], [], [3], [5]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [5] [] ∧ LexLE [] [])) h)

private theorem k16t8_cover255 : ∀ P ∈ pathPatterns 3 5 [3], HasCheckedCertificate 16 8 ([[], [], [], [3]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [3] [] ∧ LexLE [] [])) h)
      · intro q
        fin_cases q
        · exact by
            constructor
            · exact by
                intro h
                exact False.elim ((by decide : ¬ (LexLE [3] [1] ∧ LexLE [1] [1])) h)
            · intro q
              fin_cases q
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [3] [1, 1] ∧ LexLE [1, 1] [1, 1])) h)
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [3] [1, 2] ∧ LexLE [1, 2] [2, 1])) h)
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [3] [1, 3] ∧ LexLE [1, 3] [3, 1])) h)
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [3] [1, 4] ∧ LexLE [1, 4] [4, 1])) h)
        · exact by
            constructor
            · exact by
                intro h
                exact False.elim ((by decide : ¬ (LexLE [3] [2] ∧ LexLE [2] [2])) h)
            · intro q
              fin_cases q
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [3] [2, 1] ∧ LexLE [2, 1] [1, 2])) h)
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [3] [2, 2] ∧ LexLE [2, 2] [2, 2])) h)
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [3] [2, 3] ∧ LexLE [2, 3] [3, 2])) h)
        · exact by
            constructor
            · exact by
                intro _
                exact k16t8_cover256
            · intro q
              fin_cases q
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [3] [3, 1] ∧ LexLE [3, 1] [1, 3])) h)
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [3] [3, 2] ∧ LexLE [3, 2] [2, 3])) h)
        · exact by
            constructor
            · exact by
                intro _
                exact k16t8_cover257
            · intro q
              fin_cases q
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [3] [4, 1] ∧ LexLE [4, 1] [1, 4])) h)
        · exact by
            constructor
            · exact by
                intro _
                exact k16t8_cover258
            · intro q
              exact Fin.elim0 q

private theorem k16t8_cover259 : ∀ P ∈ pathPatterns 0 0 [3, 1, 1, 3], HasCheckedCertificate 16 8 ([[], [], [], [3, 1, 1, 3]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k16t8p146, Certificates.k16t8p146_check⟩

private theorem k16t8_cover260 : ∀ P ∈ pathPatterns 1 1 [3, 1, 3], HasCheckedCertificate 16 8 ([[], [], [], [3, 1, 3]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [3, 1, 3] [] ∧ LexLE [] [])) h)

private theorem k16t8_cover261 : ∀ P ∈ pathPatterns 1 0 [3, 1, 4], HasCheckedCertificate 16 8 ([[], [], [], [3, 1, 4]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [3, 1, 4] [] ∧ LexLE [] [])) h)

private theorem k16t8_cover262 : ∀ P ∈ pathPatterns 1 0 [3, 2, 3], HasCheckedCertificate 16 8 ([[], [], [], [3, 2, 3]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [3, 2, 3] [] ∧ LexLE [] [])) h)

private theorem k16t8_cover263 : ∀ P ∈ pathPatterns 2 2 [3, 3], HasCheckedCertificate 16 8 ([[], [], [], [3, 3]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [3, 3] [] ∧ LexLE [] [])) h)
      · intro q
        fin_cases q
        · exact by
            intro h
            exact False.elim ((by decide : ¬ (LexLE [3, 3] [1] ∧ LexLE [1] [1])) h)
        · exact by
            intro h
            exact False.elim ((by decide : ¬ (LexLE [3, 3] [2] ∧ LexLE [2] [2])) h)

private theorem k16t8_cover264 : ∀ P ∈ pathPatterns 2 1 [3, 4], HasCheckedCertificate 16 8 ([[], [], [], [3, 4]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [3, 4] [] ∧ LexLE [] [])) h)
      · intro q
        fin_cases q
        · exact by
            intro h
            exact False.elim ((by decide : ¬ (LexLE [3, 4] [1] ∧ LexLE [1] [1])) h)

private theorem k16t8_cover265 : ∀ P ∈ pathPatterns 2 0 [3, 5], HasCheckedCertificate 16 8 ([[], [], [], [3, 5]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [3, 5] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k16t8_seq254 : amountSequenceForall 3 5 (fun tail =>
    (LexLE [] ([3] ++ tail) ∧ LexLE ([3] ++ tail) ([3] ++ tail).reverse) →
    ∀ P ∈ pathPatterns (4 - ([3] ++ tail).length) (8 - ([3] ++ tail).sum) ([3] ++ tail),
      HasCheckedCertificate 16 8 ([[], [], []] ++ (([3] ++ tail) :: P))) :=
by
  constructor
  · exact by
      intro _
      exact k16t8_cover255
  · intro q
    fin_cases q
    · exact by
        constructor
        · exact by
            intro h
            exact False.elim ((by decide : ¬ (LexLE [] [3, 1] ∧ LexLE [3, 1] [1, 3])) h)
        · intro q
          fin_cases q
          · exact by
              constructor
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [] [3, 1, 1] ∧ LexLE [3, 1, 1] [1, 1, 3])) h)
              · intro q
                fin_cases q
                · exact by
                    intro h
                    exact False.elim ((by decide : ¬ (LexLE [] [3, 1, 1, 1] ∧ LexLE [3, 1, 1, 1] [1, 1, 1, 3])) h)
                · exact by
                    intro h
                    exact False.elim ((by decide : ¬ (LexLE [] [3, 1, 1, 2] ∧ LexLE [3, 1, 1, 2] [2, 1, 1, 3])) h)
                · exact by
                    intro _
                    exact k16t8_cover259
          · exact by
              constructor
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [] [3, 1, 2] ∧ LexLE [3, 1, 2] [2, 1, 3])) h)
              · intro q
                fin_cases q
                · exact by
                    intro h
                    exact False.elim ((by decide : ¬ (LexLE [] [3, 1, 2, 1] ∧ LexLE [3, 1, 2, 1] [1, 2, 1, 3])) h)
                · exact by
                    intro h
                    exact False.elim ((by decide : ¬ (LexLE [] [3, 1, 2, 2] ∧ LexLE [3, 1, 2, 2] [2, 2, 1, 3])) h)
          · exact by
              constructor
              · exact by
                  intro _
                  exact k16t8_cover260
              · intro q
                fin_cases q
                · exact by
                    intro h
                    exact False.elim ((by decide : ¬ (LexLE [] [3, 1, 3, 1] ∧ LexLE [3, 1, 3, 1] [1, 3, 1, 3])) h)
          · exact by
              constructor
              · exact by
                  intro _
                  exact k16t8_cover261
              · intro q
                exact Fin.elim0 q
    · exact by
        constructor
        · exact by
            intro h
            exact False.elim ((by decide : ¬ (LexLE [] [3, 2] ∧ LexLE [3, 2] [2, 3])) h)
        · intro q
          fin_cases q
          · exact by
              constructor
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [] [3, 2, 1] ∧ LexLE [3, 2, 1] [1, 2, 3])) h)
              · intro q
                fin_cases q
                · exact by
                    intro h
                    exact False.elim ((by decide : ¬ (LexLE [] [3, 2, 1, 1] ∧ LexLE [3, 2, 1, 1] [1, 1, 2, 3])) h)
                · exact by
                    intro h
                    exact False.elim ((by decide : ¬ (LexLE [] [3, 2, 1, 2] ∧ LexLE [3, 2, 1, 2] [2, 1, 2, 3])) h)
          · exact by
              constructor
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [] [3, 2, 2] ∧ LexLE [3, 2, 2] [2, 2, 3])) h)
              · intro q
                fin_cases q
                · exact by
                    intro h
                    exact False.elim ((by decide : ¬ (LexLE [] [3, 2, 2, 1] ∧ LexLE [3, 2, 2, 1] [1, 2, 2, 3])) h)
          · exact by
              constructor
              · exact by
                  intro _
                  exact k16t8_cover262
              · intro q
                exact Fin.elim0 q
    · exact by
        constructor
        · exact by
            intro _
            exact k16t8_cover263
        · intro q
          fin_cases q
          · exact by
              constructor
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [] [3, 3, 1] ∧ LexLE [3, 3, 1] [1, 3, 3])) h)
              · intro q
                fin_cases q
                · exact by
                    intro h
                    exact False.elim ((by decide : ¬ (LexLE [] [3, 3, 1, 1] ∧ LexLE [3, 3, 1, 1] [1, 1, 3, 3])) h)
          · exact by
              constructor
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [] [3, 3, 2] ∧ LexLE [3, 3, 2] [2, 3, 3])) h)
              · intro q
                exact Fin.elim0 q
    · exact by
        constructor
        · exact by
            intro _
            exact k16t8_cover264
        · intro q
          fin_cases q
          · exact by
              constructor
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [] [3, 4, 1] ∧ LexLE [3, 4, 1] [1, 4, 3])) h)
              · intro q
                exact Fin.elim0 q
    · exact by
        constructor
        · exact by
            intro _
            exact k16t8_cover265
        · intro q
          exact Fin.elim0 q

private theorem k16t8_cover267 : ∀ P ∈ pathPatterns 1 0 [4], HasCheckedCertificate 16 8 ([[], [], [], [4], [4]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [4] [] ∧ LexLE [] [])) h)

private theorem k16t8_cover266 : ∀ P ∈ pathPatterns 3 4 [4], HasCheckedCertificate 16 8 ([[], [], [], [4]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [4] [] ∧ LexLE [] [])) h)
      · intro q
        fin_cases q
        · exact by
            constructor
            · exact by
                intro h
                exact False.elim ((by decide : ¬ (LexLE [4] [1] ∧ LexLE [1] [1])) h)
            · intro q
              fin_cases q
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [4] [1, 1] ∧ LexLE [1, 1] [1, 1])) h)
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [4] [1, 2] ∧ LexLE [1, 2] [2, 1])) h)
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [4] [1, 3] ∧ LexLE [1, 3] [3, 1])) h)
        · exact by
            constructor
            · exact by
                intro h
                exact False.elim ((by decide : ¬ (LexLE [4] [2] ∧ LexLE [2] [2])) h)
            · intro q
              fin_cases q
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [4] [2, 1] ∧ LexLE [2, 1] [1, 2])) h)
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [4] [2, 2] ∧ LexLE [2, 2] [2, 2])) h)
        · exact by
            constructor
            · exact by
                intro h
                exact False.elim ((by decide : ¬ (LexLE [4] [3] ∧ LexLE [3] [3])) h)
            · intro q
              fin_cases q
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [4] [3, 1] ∧ LexLE [3, 1] [1, 3])) h)
        · exact by
            constructor
            · exact by
                intro _
                exact k16t8_cover267
            · intro q
              exact Fin.elim0 q

private theorem k16t8_cover268 : ∀ P ∈ pathPatterns 2 0 [4, 4], HasCheckedCertificate 16 8 ([[], [], [], [4, 4]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [4, 4] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k16t8_cover269 : ∀ P ∈ pathPatterns 3 3 [5], HasCheckedCertificate 16 8 ([[], [], [], [5]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [5] [] ∧ LexLE [] [])) h)
      · intro q
        fin_cases q
        · exact by
            constructor
            · exact by
                intro h
                exact False.elim ((by decide : ¬ (LexLE [5] [1] ∧ LexLE [1] [1])) h)
            · intro q
              fin_cases q
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [5] [1, 1] ∧ LexLE [1, 1] [1, 1])) h)
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [5] [1, 2] ∧ LexLE [1, 2] [2, 1])) h)
        · exact by
            constructor
            · exact by
                intro h
                exact False.elim ((by decide : ¬ (LexLE [5] [2] ∧ LexLE [2] [2])) h)
            · intro q
              fin_cases q
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [5] [2, 1] ∧ LexLE [2, 1] [1, 2])) h)
        · exact by
            constructor
            · exact by
                intro h
                exact False.elim ((by decide : ¬ (LexLE [5] [3] ∧ LexLE [3] [3])) h)
            · intro q
              exact Fin.elim0 q

private theorem k16t8_cover270 : ∀ P ∈ pathPatterns 3 2 [6], HasCheckedCertificate 16 8 ([[], [], [], [6]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [6] [] ∧ LexLE [] [])) h)
      · intro q
        fin_cases q
        · exact by
            constructor
            · exact by
                intro h
                exact False.elim ((by decide : ¬ (LexLE [6] [1] ∧ LexLE [1] [1])) h)
            · intro q
              fin_cases q
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [6] [1, 1] ∧ LexLE [1, 1] [1, 1])) h)
        · exact by
            constructor
            · exact by
                intro h
                exact False.elim ((by decide : ¬ (LexLE [6] [2] ∧ LexLE [2] [2])) h)
            · intro q
              exact Fin.elim0 q

private theorem k16t8_cover271 : ∀ P ∈ pathPatterns 3 1 [7], HasCheckedCertificate 16 8 ([[], [], [], [7]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [7] [] ∧ LexLE [] [])) h)
      · intro q
        fin_cases q
        · exact by
            constructor
            · exact by
                intro h
                exact False.elim ((by decide : ¬ (LexLE [7] [1] ∧ LexLE [1] [1])) h)
            · intro q
              exact Fin.elim0 q

private theorem k16t8_cover272 : ∀ P ∈ pathPatterns 3 0 [8], HasCheckedCertificate 16 8 ([[], [], [], [8]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [8] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k16t8_seq8 : amountSequenceForall 4 8 (fun tail =>
    (LexLE [] ([] ++ tail) ∧ LexLE ([] ++ tail) ([] ++ tail).reverse) →
    ∀ P ∈ pathPatterns (4 - ([] ++ tail).length) (8 - ([] ++ tail).sum) ([] ++ tail),
      HasCheckedCertificate 16 8 ([[], [], []] ++ (([] ++ tail) :: P))) :=
by
  constructor
  · exact by
      intro _
      exact k16t8_cover9
  · intro q
    fin_cases q
    · exact k16t8_seq123

    · exact k16t8_seq217

    · exact k16t8_seq254

    · exact by
        constructor
        · exact by
            intro _
            exact k16t8_cover266
        · intro q
          fin_cases q
          · exact by
              constructor
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [] [4, 1] ∧ LexLE [4, 1] [1, 4])) h)
              · intro q
                fin_cases q
                · exact by
                    constructor
                    · exact by
                        intro h
                        exact False.elim ((by decide : ¬ (LexLE [] [4, 1, 1] ∧ LexLE [4, 1, 1] [1, 1, 4])) h)
                    · intro q
                      fin_cases q
                      · exact by
                          intro h
                          exact False.elim ((by decide : ¬ (LexLE [] [4, 1, 1, 1] ∧ LexLE [4, 1, 1, 1] [1, 1, 1, 4])) h)
                      · exact by
                          intro h
                          exact False.elim ((by decide : ¬ (LexLE [] [4, 1, 1, 2] ∧ LexLE [4, 1, 1, 2] [2, 1, 1, 4])) h)
                · exact by
                    constructor
                    · exact by
                        intro h
                        exact False.elim ((by decide : ¬ (LexLE [] [4, 1, 2] ∧ LexLE [4, 1, 2] [2, 1, 4])) h)
                    · intro q
                      fin_cases q
                      · exact by
                          intro h
                          exact False.elim ((by decide : ¬ (LexLE [] [4, 1, 2, 1] ∧ LexLE [4, 1, 2, 1] [1, 2, 1, 4])) h)
                · exact by
                    constructor
                    · exact by
                        intro h
                        exact False.elim ((by decide : ¬ (LexLE [] [4, 1, 3] ∧ LexLE [4, 1, 3] [3, 1, 4])) h)
                    · intro q
                      exact Fin.elim0 q
          · exact by
              constructor
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [] [4, 2] ∧ LexLE [4, 2] [2, 4])) h)
              · intro q
                fin_cases q
                · exact by
                    constructor
                    · exact by
                        intro h
                        exact False.elim ((by decide : ¬ (LexLE [] [4, 2, 1] ∧ LexLE [4, 2, 1] [1, 2, 4])) h)
                    · intro q
                      fin_cases q
                      · exact by
                          intro h
                          exact False.elim ((by decide : ¬ (LexLE [] [4, 2, 1, 1] ∧ LexLE [4, 2, 1, 1] [1, 1, 2, 4])) h)
                · exact by
                    constructor
                    · exact by
                        intro h
                        exact False.elim ((by decide : ¬ (LexLE [] [4, 2, 2] ∧ LexLE [4, 2, 2] [2, 2, 4])) h)
                    · intro q
                      exact Fin.elim0 q
          · exact by
              constructor
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [] [4, 3] ∧ LexLE [4, 3] [3, 4])) h)
              · intro q
                fin_cases q
                · exact by
                    constructor
                    · exact by
                        intro h
                        exact False.elim ((by decide : ¬ (LexLE [] [4, 3, 1] ∧ LexLE [4, 3, 1] [1, 3, 4])) h)
                    · intro q
                      exact Fin.elim0 q
          · exact by
              constructor
              · exact by
                  intro _
                  exact k16t8_cover268
              · intro q
                exact Fin.elim0 q
    · exact by
        constructor
        · exact by
            intro _
            exact k16t8_cover269
        · intro q
          fin_cases q
          · exact by
              constructor
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [] [5, 1] ∧ LexLE [5, 1] [1, 5])) h)
              · intro q
                fin_cases q
                · exact by
                    constructor
                    · exact by
                        intro h
                        exact False.elim ((by decide : ¬ (LexLE [] [5, 1, 1] ∧ LexLE [5, 1, 1] [1, 1, 5])) h)
                    · intro q
                      fin_cases q
                      · exact by
                          intro h
                          exact False.elim ((by decide : ¬ (LexLE [] [5, 1, 1, 1] ∧ LexLE [5, 1, 1, 1] [1, 1, 1, 5])) h)
                · exact by
                    constructor
                    · exact by
                        intro h
                        exact False.elim ((by decide : ¬ (LexLE [] [5, 1, 2] ∧ LexLE [5, 1, 2] [2, 1, 5])) h)
                    · intro q
                      exact Fin.elim0 q
          · exact by
              constructor
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [] [5, 2] ∧ LexLE [5, 2] [2, 5])) h)
              · intro q
                fin_cases q
                · exact by
                    constructor
                    · exact by
                        intro h
                        exact False.elim ((by decide : ¬ (LexLE [] [5, 2, 1] ∧ LexLE [5, 2, 1] [1, 2, 5])) h)
                    · intro q
                      exact Fin.elim0 q
          · exact by
              constructor
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [] [5, 3] ∧ LexLE [5, 3] [3, 5])) h)
              · intro q
                exact Fin.elim0 q
    · exact by
        constructor
        · exact by
            intro _
            exact k16t8_cover270
        · intro q
          fin_cases q
          · exact by
              constructor
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [] [6, 1] ∧ LexLE [6, 1] [1, 6])) h)
              · intro q
                fin_cases q
                · exact by
                    constructor
                    · exact by
                        intro h
                        exact False.elim ((by decide : ¬ (LexLE [] [6, 1, 1] ∧ LexLE [6, 1, 1] [1, 1, 6])) h)
                    · intro q
                      exact Fin.elim0 q
          · exact by
              constructor
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [] [6, 2] ∧ LexLE [6, 2] [2, 6])) h)
              · intro q
                exact Fin.elim0 q
    · exact by
        constructor
        · exact by
            intro _
            exact k16t8_cover271
        · intro q
          fin_cases q
          · exact by
              constructor
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [] [7, 1] ∧ LexLE [7, 1] [1, 7])) h)
              · intro q
                exact Fin.elim0 q
    · exact by
        constructor
        · exact by
            intro _
            exact k16t8_cover272
        · intro q
          exact Fin.elim0 q

private theorem k16t8_cover7 : ∀ P ∈ pathPatterns 5 8 [], HasCheckedCertificate 16 8 ([[], [], []] ++ P) := by
  apply pathPatterns_forall_step
  exact k16t8_seq8


private theorem k16t8_cover277 : ∀ P ∈ pathPatterns 0 5 [1], HasCheckedCertificate 16 8 ([[], [], [1], [1], [1]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k16t8p147, Certificates.k16t8p147_check⟩

private theorem k16t8_cover278 : ∀ P ∈ pathPatterns 0 4 [2], HasCheckedCertificate 16 8 ([[], [], [1], [1], [2]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k16t8p148, Certificates.k16t8p148_check⟩

private theorem k16t8_cover279 : ∀ P ∈ pathPatterns 0 3 [3], HasCheckedCertificate 16 8 ([[], [], [1], [1], [3]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k16t8p149, Certificates.k16t8p149_check⟩

private theorem k16t8_cover280 : ∀ P ∈ pathPatterns 0 2 [4], HasCheckedCertificate 16 8 ([[], [], [1], [1], [4]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k16t8p150, Certificates.k16t8p150_check⟩

private theorem k16t8_cover281 : ∀ P ∈ pathPatterns 0 1 [5], HasCheckedCertificate 16 8 ([[], [], [1], [1], [5]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k16t8p151, Certificates.k16t8p151_check⟩

private theorem k16t8_cover282 : ∀ P ∈ pathPatterns 0 0 [6], HasCheckedCertificate 16 8 ([[], [], [1], [1], [6]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k16t8p152, Certificates.k16t8p152_check⟩

private theorem k16t8_cover276 : ∀ P ∈ pathPatterns 2 6 [1], HasCheckedCertificate 16 8 ([[], [], [1], [1]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [1] [] ∧ LexLE [] [])) h)
      · intro q
        fin_cases q
        · exact by
            intro _
            exact k16t8_cover277
        · exact by
            intro _
            exact k16t8_cover278
        · exact by
            intro _
            exact k16t8_cover279
        · exact by
            intro _
            exact k16t8_cover280
        · exact by
            intro _
            exact k16t8_cover281
        · exact by
            intro _
            exact k16t8_cover282

private theorem k16t8_cover283 : ∀ P ∈ pathPatterns 1 5 [1, 1], HasCheckedCertificate 16 8 ([[], [], [1], [1, 1]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [1, 1] [] ∧ LexLE [] [])) h)

private theorem k16t8_cover284 : ∀ P ∈ pathPatterns 0 4 [1, 1, 1], HasCheckedCertificate 16 8 ([[], [], [1], [1, 1, 1]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k16t8p153, Certificates.k16t8p153_check⟩

private theorem k16t8_cover285 : ∀ P ∈ pathPatterns 0 3 [1, 1, 2], HasCheckedCertificate 16 8 ([[], [], [1], [1, 1, 2]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k16t8p154, Certificates.k16t8p154_check⟩

private theorem k16t8_cover286 : ∀ P ∈ pathPatterns 0 2 [1, 1, 3], HasCheckedCertificate 16 8 ([[], [], [1], [1, 1, 3]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k16t8p155, Certificates.k16t8p155_check⟩

private theorem k16t8_cover287 : ∀ P ∈ pathPatterns 0 1 [1, 1, 4], HasCheckedCertificate 16 8 ([[], [], [1], [1, 1, 4]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k16t8p156, Certificates.k16t8p156_check⟩

private theorem k16t8_cover288 : ∀ P ∈ pathPatterns 0 0 [1, 1, 5], HasCheckedCertificate 16 8 ([[], [], [1], [1, 1, 5]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k16t8p157, Certificates.k16t8p157_check⟩

private theorem k16t8_cover289 : ∀ P ∈ pathPatterns 1 4 [1, 2], HasCheckedCertificate 16 8 ([[], [], [1], [1, 2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [1, 2] [] ∧ LexLE [] [])) h)

private theorem k16t8_cover290 : ∀ P ∈ pathPatterns 0 3 [1, 2, 1], HasCheckedCertificate 16 8 ([[], [], [1], [1, 2, 1]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k16t8p158, Certificates.k16t8p158_check⟩

private theorem k16t8_cover291 : ∀ P ∈ pathPatterns 0 2 [1, 2, 2], HasCheckedCertificate 16 8 ([[], [], [1], [1, 2, 2]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k16t8p159, Certificates.k16t8p159_check⟩

private theorem k16t8_cover292 : ∀ P ∈ pathPatterns 0 1 [1, 2, 3], HasCheckedCertificate 16 8 ([[], [], [1], [1, 2, 3]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k16t8p160, Certificates.k16t8p160_check⟩

private theorem k16t8_cover293 : ∀ P ∈ pathPatterns 0 0 [1, 2, 4], HasCheckedCertificate 16 8 ([[], [], [1], [1, 2, 4]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k16t8p161, Certificates.k16t8p161_check⟩

private theorem k16t8_cover294 : ∀ P ∈ pathPatterns 1 3 [1, 3], HasCheckedCertificate 16 8 ([[], [], [1], [1, 3]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [1, 3] [] ∧ LexLE [] [])) h)

private theorem k16t8_cover295 : ∀ P ∈ pathPatterns 0 2 [1, 3, 1], HasCheckedCertificate 16 8 ([[], [], [1], [1, 3, 1]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k16t8p162, Certificates.k16t8p162_check⟩

private theorem k16t8_cover296 : ∀ P ∈ pathPatterns 0 1 [1, 3, 2], HasCheckedCertificate 16 8 ([[], [], [1], [1, 3, 2]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k16t8p163, Certificates.k16t8p163_check⟩

private theorem k16t8_cover297 : ∀ P ∈ pathPatterns 0 0 [1, 3, 3], HasCheckedCertificate 16 8 ([[], [], [1], [1, 3, 3]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k16t8p164, Certificates.k16t8p164_check⟩

private theorem k16t8_cover298 : ∀ P ∈ pathPatterns 1 2 [1, 4], HasCheckedCertificate 16 8 ([[], [], [1], [1, 4]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [1, 4] [] ∧ LexLE [] [])) h)

private theorem k16t8_cover299 : ∀ P ∈ pathPatterns 0 1 [1, 4, 1], HasCheckedCertificate 16 8 ([[], [], [1], [1, 4, 1]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k16t8p165, Certificates.k16t8p165_check⟩

private theorem k16t8_cover300 : ∀ P ∈ pathPatterns 0 0 [1, 4, 2], HasCheckedCertificate 16 8 ([[], [], [1], [1, 4, 2]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k16t8p166, Certificates.k16t8p166_check⟩

private theorem k16t8_cover301 : ∀ P ∈ pathPatterns 1 1 [1, 5], HasCheckedCertificate 16 8 ([[], [], [1], [1, 5]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [1, 5] [] ∧ LexLE [] [])) h)

private theorem k16t8_cover302 : ∀ P ∈ pathPatterns 0 0 [1, 5, 1], HasCheckedCertificate 16 8 ([[], [], [1], [1, 5, 1]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k16t8p167, Certificates.k16t8p167_check⟩

private theorem k16t8_cover303 : ∀ P ∈ pathPatterns 1 0 [1, 6], HasCheckedCertificate 16 8 ([[], [], [1], [1, 6]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [1, 6] [] ∧ LexLE [] [])) h)

private theorem k16t8_cover305 : ∀ P ∈ pathPatterns 0 3 [2], HasCheckedCertificate 16 8 ([[], [], [1], [2], [2]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k16t8p168, Certificates.k16t8p168_check⟩

private theorem k16t8_cover306 : ∀ P ∈ pathPatterns 0 2 [3], HasCheckedCertificate 16 8 ([[], [], [1], [2], [3]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k16t8p169, Certificates.k16t8p169_check⟩

private theorem k16t8_cover307 : ∀ P ∈ pathPatterns 0 1 [4], HasCheckedCertificate 16 8 ([[], [], [1], [2], [4]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k16t8p170, Certificates.k16t8p170_check⟩

private theorem k16t8_cover308 : ∀ P ∈ pathPatterns 0 0 [5], HasCheckedCertificate 16 8 ([[], [], [1], [2], [5]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k16t8p171, Certificates.k16t8p171_check⟩

private theorem k16t8_cover304 : ∀ P ∈ pathPatterns 2 5 [2], HasCheckedCertificate 16 8 ([[], [], [1], [2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [2] [] ∧ LexLE [] [])) h)
      · intro q
        fin_cases q
        · exact by
            intro h
            exact False.elim ((by decide : ¬ (LexLE [2] [1] ∧ LexLE [1] [1])) h)
        · exact by
            intro _
            exact k16t8_cover305
        · exact by
            intro _
            exact k16t8_cover306
        · exact by
            intro _
            exact k16t8_cover307
        · exact by
            intro _
            exact k16t8_cover308

private theorem k16t8_cover309 : ∀ P ∈ pathPatterns 0 2 [2, 1, 2], HasCheckedCertificate 16 8 ([[], [], [1], [2, 1, 2]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k16t8p172, Certificates.k16t8p172_check⟩

private theorem k16t8_cover310 : ∀ P ∈ pathPatterns 0 1 [2, 1, 3], HasCheckedCertificate 16 8 ([[], [], [1], [2, 1, 3]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k16t8p173, Certificates.k16t8p173_check⟩

private theorem k16t8_cover311 : ∀ P ∈ pathPatterns 0 0 [2, 1, 4], HasCheckedCertificate 16 8 ([[], [], [1], [2, 1, 4]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k16t8p174, Certificates.k16t8p174_check⟩

private theorem k16t8_cover312 : ∀ P ∈ pathPatterns 1 3 [2, 2], HasCheckedCertificate 16 8 ([[], [], [1], [2, 2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [2, 2] [] ∧ LexLE [] [])) h)

private theorem k16t8_cover313 : ∀ P ∈ pathPatterns 0 1 [2, 2, 2], HasCheckedCertificate 16 8 ([[], [], [1], [2, 2, 2]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k16t8p175, Certificates.k16t8p175_check⟩

private theorem k16t8_cover314 : ∀ P ∈ pathPatterns 0 0 [2, 2, 3], HasCheckedCertificate 16 8 ([[], [], [1], [2, 2, 3]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k16t8p176, Certificates.k16t8p176_check⟩

private theorem k16t8_cover315 : ∀ P ∈ pathPatterns 1 2 [2, 3], HasCheckedCertificate 16 8 ([[], [], [1], [2, 3]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [2, 3] [] ∧ LexLE [] [])) h)

private theorem k16t8_cover316 : ∀ P ∈ pathPatterns 0 0 [2, 3, 2], HasCheckedCertificate 16 8 ([[], [], [1], [2, 3, 2]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k16t8p177, Certificates.k16t8p177_check⟩

private theorem k16t8_cover317 : ∀ P ∈ pathPatterns 1 1 [2, 4], HasCheckedCertificate 16 8 ([[], [], [1], [2, 4]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [2, 4] [] ∧ LexLE [] [])) h)

private theorem k16t8_cover318 : ∀ P ∈ pathPatterns 1 0 [2, 5], HasCheckedCertificate 16 8 ([[], [], [1], [2, 5]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [2, 5] [] ∧ LexLE [] [])) h)

private theorem k16t8_cover320 : ∀ P ∈ pathPatterns 0 1 [3], HasCheckedCertificate 16 8 ([[], [], [1], [3], [3]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k16t8p178, Certificates.k16t8p178_check⟩

private theorem k16t8_cover321 : ∀ P ∈ pathPatterns 0 0 [4], HasCheckedCertificate 16 8 ([[], [], [1], [3], [4]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k16t8p179, Certificates.k16t8p179_check⟩

private theorem k16t8_cover319 : ∀ P ∈ pathPatterns 2 4 [3], HasCheckedCertificate 16 8 ([[], [], [1], [3]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [3] [] ∧ LexLE [] [])) h)
      · intro q
        fin_cases q
        · exact by
            intro h
            exact False.elim ((by decide : ¬ (LexLE [3] [1] ∧ LexLE [1] [1])) h)
        · exact by
            intro h
            exact False.elim ((by decide : ¬ (LexLE [3] [2] ∧ LexLE [2] [2])) h)
        · exact by
            intro _
            exact k16t8_cover320
        · exact by
            intro _
            exact k16t8_cover321

private theorem k16t8_cover322 : ∀ P ∈ pathPatterns 0 0 [3, 1, 3], HasCheckedCertificate 16 8 ([[], [], [1], [3, 1, 3]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k16t8p180, Certificates.k16t8p180_check⟩

private theorem k16t8_cover323 : ∀ P ∈ pathPatterns 1 1 [3, 3], HasCheckedCertificate 16 8 ([[], [], [1], [3, 3]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [3, 3] [] ∧ LexLE [] [])) h)

private theorem k16t8_cover324 : ∀ P ∈ pathPatterns 1 0 [3, 4], HasCheckedCertificate 16 8 ([[], [], [1], [3, 4]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [3, 4] [] ∧ LexLE [] [])) h)

private theorem k16t8_cover325 : ∀ P ∈ pathPatterns 2 3 [4], HasCheckedCertificate 16 8 ([[], [], [1], [4]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [4] [] ∧ LexLE [] [])) h)
      · intro q
        fin_cases q
        · exact by
            intro h
            exact False.elim ((by decide : ¬ (LexLE [4] [1] ∧ LexLE [1] [1])) h)
        · exact by
            intro h
            exact False.elim ((by decide : ¬ (LexLE [4] [2] ∧ LexLE [2] [2])) h)
        · exact by
            intro h
            exact False.elim ((by decide : ¬ (LexLE [4] [3] ∧ LexLE [3] [3])) h)

private theorem k16t8_cover326 : ∀ P ∈ pathPatterns 2 2 [5], HasCheckedCertificate 16 8 ([[], [], [1], [5]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [5] [] ∧ LexLE [] [])) h)
      · intro q
        fin_cases q
        · exact by
            intro h
            exact False.elim ((by decide : ¬ (LexLE [5] [1] ∧ LexLE [1] [1])) h)
        · exact by
            intro h
            exact False.elim ((by decide : ¬ (LexLE [5] [2] ∧ LexLE [2] [2])) h)

private theorem k16t8_cover327 : ∀ P ∈ pathPatterns 2 1 [6], HasCheckedCertificate 16 8 ([[], [], [1], [6]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [6] [] ∧ LexLE [] [])) h)
      · intro q
        fin_cases q
        · exact by
            intro h
            exact False.elim ((by decide : ¬ (LexLE [6] [1] ∧ LexLE [1] [1])) h)

private theorem k16t8_cover328 : ∀ P ∈ pathPatterns 2 0 [7], HasCheckedCertificate 16 8 ([[], [], [1], [7]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [7] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k16t8_seq275 : amountSequenceForall 3 7 (fun tail =>
    (LexLE [1] ([] ++ tail) ∧ LexLE ([] ++ tail) ([] ++ tail).reverse) →
    ∀ P ∈ pathPatterns (3 - ([] ++ tail).length) (7 - ([] ++ tail).sum) ([] ++ tail),
      HasCheckedCertificate 16 8 ([[], [], [1]] ++ (([] ++ tail) :: P))) :=
by
  constructor
  · exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [1] [] ∧ LexLE [] [])) h)
  · intro q
    fin_cases q
    · exact by
        constructor
        · exact by
            intro _
            exact k16t8_cover276
        · intro q
          fin_cases q
          · exact by
              constructor
              · exact by
                  intro _
                  exact k16t8_cover283
              · intro q
                fin_cases q
                · exact by
                    intro _
                    exact k16t8_cover284
                · exact by
                    intro _
                    exact k16t8_cover285
                · exact by
                    intro _
                    exact k16t8_cover286
                · exact by
                    intro _
                    exact k16t8_cover287
                · exact by
                    intro _
                    exact k16t8_cover288
          · exact by
              constructor
              · exact by
                  intro _
                  exact k16t8_cover289
              · intro q
                fin_cases q
                · exact by
                    intro _
                    exact k16t8_cover290
                · exact by
                    intro _
                    exact k16t8_cover291
                · exact by
                    intro _
                    exact k16t8_cover292
                · exact by
                    intro _
                    exact k16t8_cover293
          · exact by
              constructor
              · exact by
                  intro _
                  exact k16t8_cover294
              · intro q
                fin_cases q
                · exact by
                    intro _
                    exact k16t8_cover295
                · exact by
                    intro _
                    exact k16t8_cover296
                · exact by
                    intro _
                    exact k16t8_cover297
          · exact by
              constructor
              · exact by
                  intro _
                  exact k16t8_cover298
              · intro q
                fin_cases q
                · exact by
                    intro _
                    exact k16t8_cover299
                · exact by
                    intro _
                    exact k16t8_cover300
          · exact by
              constructor
              · exact by
                  intro _
                  exact k16t8_cover301
              · intro q
                fin_cases q
                · exact by
                    intro _
                    exact k16t8_cover302
          · exact by
              constructor
              · exact by
                  intro _
                  exact k16t8_cover303
              · intro q
                exact Fin.elim0 q
    · exact by
        constructor
        · exact by
            intro _
            exact k16t8_cover304
        · intro q
          fin_cases q
          · exact by
              constructor
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [1] [2, 1] ∧ LexLE [2, 1] [1, 2])) h)
              · intro q
                fin_cases q
                · exact by
                    intro h
                    exact False.elim ((by decide : ¬ (LexLE [1] [2, 1, 1] ∧ LexLE [2, 1, 1] [1, 1, 2])) h)
                · exact by
                    intro _
                    exact k16t8_cover309
                · exact by
                    intro _
                    exact k16t8_cover310
                · exact by
                    intro _
                    exact k16t8_cover311
          · exact by
              constructor
              · exact by
                  intro _
                  exact k16t8_cover312
              · intro q
                fin_cases q
                · exact by
                    intro h
                    exact False.elim ((by decide : ¬ (LexLE [1] [2, 2, 1] ∧ LexLE [2, 2, 1] [1, 2, 2])) h)
                · exact by
                    intro _
                    exact k16t8_cover313
                · exact by
                    intro _
                    exact k16t8_cover314
          · exact by
              constructor
              · exact by
                  intro _
                  exact k16t8_cover315
              · intro q
                fin_cases q
                · exact by
                    intro h
                    exact False.elim ((by decide : ¬ (LexLE [1] [2, 3, 1] ∧ LexLE [2, 3, 1] [1, 3, 2])) h)
                · exact by
                    intro _
                    exact k16t8_cover316
          · exact by
              constructor
              · exact by
                  intro _
                  exact k16t8_cover317
              · intro q
                fin_cases q
                · exact by
                    intro h
                    exact False.elim ((by decide : ¬ (LexLE [1] [2, 4, 1] ∧ LexLE [2, 4, 1] [1, 4, 2])) h)
          · exact by
              constructor
              · exact by
                  intro _
                  exact k16t8_cover318
              · intro q
                exact Fin.elim0 q
    · exact by
        constructor
        · exact by
            intro _
            exact k16t8_cover319
        · intro q
          fin_cases q
          · exact by
              constructor
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [1] [3, 1] ∧ LexLE [3, 1] [1, 3])) h)
              · intro q
                fin_cases q
                · exact by
                    intro h
                    exact False.elim ((by decide : ¬ (LexLE [1] [3, 1, 1] ∧ LexLE [3, 1, 1] [1, 1, 3])) h)
                · exact by
                    intro h
                    exact False.elim ((by decide : ¬ (LexLE [1] [3, 1, 2] ∧ LexLE [3, 1, 2] [2, 1, 3])) h)
                · exact by
                    intro _
                    exact k16t8_cover322
          · exact by
              constructor
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [1] [3, 2] ∧ LexLE [3, 2] [2, 3])) h)
              · intro q
                fin_cases q
                · exact by
                    intro h
                    exact False.elim ((by decide : ¬ (LexLE [1] [3, 2, 1] ∧ LexLE [3, 2, 1] [1, 2, 3])) h)
                · exact by
                    intro h
                    exact False.elim ((by decide : ¬ (LexLE [1] [3, 2, 2] ∧ LexLE [3, 2, 2] [2, 2, 3])) h)
          · exact by
              constructor
              · exact by
                  intro _
                  exact k16t8_cover323
              · intro q
                fin_cases q
                · exact by
                    intro h
                    exact False.elim ((by decide : ¬ (LexLE [1] [3, 3, 1] ∧ LexLE [3, 3, 1] [1, 3, 3])) h)
          · exact by
              constructor
              · exact by
                  intro _
                  exact k16t8_cover324
              · intro q
                exact Fin.elim0 q
    · exact by
        constructor
        · exact by
            intro _
            exact k16t8_cover325
        · intro q
          fin_cases q
          · exact by
              constructor
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [1] [4, 1] ∧ LexLE [4, 1] [1, 4])) h)
              · intro q
                fin_cases q
                · exact by
                    intro h
                    exact False.elim ((by decide : ¬ (LexLE [1] [4, 1, 1] ∧ LexLE [4, 1, 1] [1, 1, 4])) h)
                · exact by
                    intro h
                    exact False.elim ((by decide : ¬ (LexLE [1] [4, 1, 2] ∧ LexLE [4, 1, 2] [2, 1, 4])) h)
          · exact by
              constructor
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [1] [4, 2] ∧ LexLE [4, 2] [2, 4])) h)
              · intro q
                fin_cases q
                · exact by
                    intro h
                    exact False.elim ((by decide : ¬ (LexLE [1] [4, 2, 1] ∧ LexLE [4, 2, 1] [1, 2, 4])) h)
          · exact by
              constructor
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [1] [4, 3] ∧ LexLE [4, 3] [3, 4])) h)
              · intro q
                exact Fin.elim0 q
    · exact by
        constructor
        · exact by
            intro _
            exact k16t8_cover326
        · intro q
          fin_cases q
          · exact by
              constructor
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [1] [5, 1] ∧ LexLE [5, 1] [1, 5])) h)
              · intro q
                fin_cases q
                · exact by
                    intro h
                    exact False.elim ((by decide : ¬ (LexLE [1] [5, 1, 1] ∧ LexLE [5, 1, 1] [1, 1, 5])) h)
          · exact by
              constructor
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [1] [5, 2] ∧ LexLE [5, 2] [2, 5])) h)
              · intro q
                exact Fin.elim0 q
    · exact by
        constructor
        · exact by
            intro _
            exact k16t8_cover327
        · intro q
          fin_cases q
          · exact by
              constructor
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [1] [6, 1] ∧ LexLE [6, 1] [1, 6])) h)
              · intro q
                exact Fin.elim0 q
    · exact by
        constructor
        · exact by
            intro _
            exact k16t8_cover328
        · intro q
          exact Fin.elim0 q

private theorem k16t8_cover274 : ∀ P ∈ pathPatterns 4 7 [1], HasCheckedCertificate 16 8 ([[], [], [1]] ++ P) := by
  apply pathPatterns_forall_step
  exact k16t8_seq275


private theorem k16t8_cover331 : ∀ P ∈ pathPatterns 0 4 [1, 1], HasCheckedCertificate 16 8 ([[], [], [1, 1], [1, 1]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k16t8p181, Certificates.k16t8p181_check⟩

private theorem k16t8_cover332 : ∀ P ∈ pathPatterns 0 3 [1, 2], HasCheckedCertificate 16 8 ([[], [], [1, 1], [1, 2]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k16t8p182, Certificates.k16t8p182_check⟩

private theorem k16t8_cover333 : ∀ P ∈ pathPatterns 0 2 [1, 3], HasCheckedCertificate 16 8 ([[], [], [1, 1], [1, 3]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k16t8p183, Certificates.k16t8p183_check⟩

private theorem k16t8_cover334 : ∀ P ∈ pathPatterns 0 1 [1, 4], HasCheckedCertificate 16 8 ([[], [], [1, 1], [1, 4]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k16t8p184, Certificates.k16t8p184_check⟩

private theorem k16t8_cover335 : ∀ P ∈ pathPatterns 0 0 [1, 5], HasCheckedCertificate 16 8 ([[], [], [1, 1], [1, 5]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k16t8p185, Certificates.k16t8p185_check⟩

private theorem k16t8_cover336 : ∀ P ∈ pathPatterns 1 4 [2], HasCheckedCertificate 16 8 ([[], [], [1, 1], [2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [2] [] ∧ LexLE [] [])) h)

private theorem k16t8_cover337 : ∀ P ∈ pathPatterns 0 2 [2, 2], HasCheckedCertificate 16 8 ([[], [], [1, 1], [2, 2]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k16t8p186, Certificates.k16t8p186_check⟩

private theorem k16t8_cover338 : ∀ P ∈ pathPatterns 0 1 [2, 3], HasCheckedCertificate 16 8 ([[], [], [1, 1], [2, 3]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k16t8p187, Certificates.k16t8p187_check⟩

private theorem k16t8_cover339 : ∀ P ∈ pathPatterns 0 0 [2, 4], HasCheckedCertificate 16 8 ([[], [], [1, 1], [2, 4]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k16t8p188, Certificates.k16t8p188_check⟩

private theorem k16t8_cover340 : ∀ P ∈ pathPatterns 1 3 [3], HasCheckedCertificate 16 8 ([[], [], [1, 1], [3]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [3] [] ∧ LexLE [] [])) h)

private theorem k16t8_cover341 : ∀ P ∈ pathPatterns 0 0 [3, 3], HasCheckedCertificate 16 8 ([[], [], [1, 1], [3, 3]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k16t8p189, Certificates.k16t8p189_check⟩

private theorem k16t8_cover342 : ∀ P ∈ pathPatterns 1 2 [4], HasCheckedCertificate 16 8 ([[], [], [1, 1], [4]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [4] [] ∧ LexLE [] [])) h)

private theorem k16t8_cover343 : ∀ P ∈ pathPatterns 1 1 [5], HasCheckedCertificate 16 8 ([[], [], [1, 1], [5]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [5] [] ∧ LexLE [] [])) h)

private theorem k16t8_cover344 : ∀ P ∈ pathPatterns 1 0 [6], HasCheckedCertificate 16 8 ([[], [], [1, 1], [6]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [6] [] ∧ LexLE [] [])) h)

private theorem k16t8_cover330 : ∀ P ∈ pathPatterns 3 6 [1, 1], HasCheckedCertificate 16 8 ([[], [], [1, 1]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [1, 1] [] ∧ LexLE [] [])) h)
      · intro q
        fin_cases q
        · exact by
            constructor
            · exact by
                intro h
                exact False.elim ((by decide : ¬ (LexLE [1, 1] [1] ∧ LexLE [1] [1])) h)
            · intro q
              fin_cases q
              · exact by
                  intro _
                  exact k16t8_cover331
              · exact by
                  intro _
                  exact k16t8_cover332
              · exact by
                  intro _
                  exact k16t8_cover333
              · exact by
                  intro _
                  exact k16t8_cover334
              · exact by
                  intro _
                  exact k16t8_cover335
        · exact by
            constructor
            · exact by
                intro _
                exact k16t8_cover336
            · intro q
              fin_cases q
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [1, 1] [2, 1] ∧ LexLE [2, 1] [1, 2])) h)
              · exact by
                  intro _
                  exact k16t8_cover337
              · exact by
                  intro _
                  exact k16t8_cover338
              · exact by
                  intro _
                  exact k16t8_cover339
        · exact by
            constructor
            · exact by
                intro _
                exact k16t8_cover340
            · intro q
              fin_cases q
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [1, 1] [3, 1] ∧ LexLE [3, 1] [1, 3])) h)
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [1, 1] [3, 2] ∧ LexLE [3, 2] [2, 3])) h)
              · exact by
                  intro _
                  exact k16t8_cover341
        · exact by
            constructor
            · exact by
                intro _
                exact k16t8_cover342
            · intro q
              fin_cases q
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [1, 1] [4, 1] ∧ LexLE [4, 1] [1, 4])) h)
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [1, 1] [4, 2] ∧ LexLE [4, 2] [2, 4])) h)
        · exact by
            constructor
            · exact by
                intro _
                exact k16t8_cover343
            · intro q
              fin_cases q
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [1, 1] [5, 1] ∧ LexLE [5, 1] [1, 5])) h)
        · exact by
            constructor
            · exact by
                intro _
                exact k16t8_cover344
            · intro q
              exact Fin.elim0 q

private theorem k16t8_cover346 : ∀ P ∈ pathPatterns 0 3 [2], HasCheckedCertificate 16 8 ([[], [], [1, 1, 1], [2]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k16t8p190, Certificates.k16t8p190_check⟩

private theorem k16t8_cover347 : ∀ P ∈ pathPatterns 0 2 [3], HasCheckedCertificate 16 8 ([[], [], [1, 1, 1], [3]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k16t8p191, Certificates.k16t8p191_check⟩

private theorem k16t8_cover348 : ∀ P ∈ pathPatterns 0 1 [4], HasCheckedCertificate 16 8 ([[], [], [1, 1, 1], [4]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k16t8p192, Certificates.k16t8p192_check⟩

private theorem k16t8_cover349 : ∀ P ∈ pathPatterns 0 0 [5], HasCheckedCertificate 16 8 ([[], [], [1, 1, 1], [5]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k16t8p193, Certificates.k16t8p193_check⟩

private theorem k16t8_cover345 : ∀ P ∈ pathPatterns 2 5 [1, 1, 1], HasCheckedCertificate 16 8 ([[], [], [1, 1, 1]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [1, 1, 1] [] ∧ LexLE [] [])) h)
      · intro q
        fin_cases q
        · exact by
            intro h
            exact False.elim ((by decide : ¬ (LexLE [1, 1, 1] [1] ∧ LexLE [1] [1])) h)
        · exact by
            intro _
            exact k16t8_cover346
        · exact by
            intro _
            exact k16t8_cover347
        · exact by
            intro _
            exact k16t8_cover348
        · exact by
            intro _
            exact k16t8_cover349

private theorem k16t8_cover350 : ∀ P ∈ pathPatterns 1 4 [1, 1, 1, 1], HasCheckedCertificate 16 8 ([[], [], [1, 1, 1, 1]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [1, 1, 1, 1] [] ∧ LexLE [] [])) h)

private theorem k16t8_cover351 : ∀ P ∈ pathPatterns 0 3 [1, 1, 1, 1, 1], HasCheckedCertificate 16 8 ([[], [], [1, 1, 1, 1, 1]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k16t8p194, Certificates.k16t8p194_check⟩

private theorem k16t8_cover352 : ∀ P ∈ pathPatterns 0 2 [1, 1, 1, 1, 2], HasCheckedCertificate 16 8 ([[], [], [1, 1, 1, 1, 2]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k16t8p195, Certificates.k16t8p195_check⟩

private theorem k16t8_cover353 : ∀ P ∈ pathPatterns 0 1 [1, 1, 1, 1, 3], HasCheckedCertificate 16 8 ([[], [], [1, 1, 1, 1, 3]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k16t8p196, Certificates.k16t8p196_check⟩

private theorem k16t8_cover354 : ∀ P ∈ pathPatterns 0 0 [1, 1, 1, 1, 4], HasCheckedCertificate 16 8 ([[], [], [1, 1, 1, 1, 4]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k16t8p197, Certificates.k16t8p197_check⟩

private theorem k16t8_cover355 : ∀ P ∈ pathPatterns 1 3 [1, 1, 1, 2], HasCheckedCertificate 16 8 ([[], [], [1, 1, 1, 2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [1, 1, 1, 2] [] ∧ LexLE [] [])) h)

private theorem k16t8_cover356 : ∀ P ∈ pathPatterns 0 2 [1, 1, 1, 2, 1], HasCheckedCertificate 16 8 ([[], [], [1, 1, 1, 2, 1]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k16t8p198, Certificates.k16t8p198_check⟩

private theorem k16t8_cover357 : ∀ P ∈ pathPatterns 0 1 [1, 1, 1, 2, 2], HasCheckedCertificate 16 8 ([[], [], [1, 1, 1, 2, 2]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k16t8p199, Certificates.k16t8p199_check⟩

private theorem k16t8_cover358 : ∀ P ∈ pathPatterns 0 0 [1, 1, 1, 2, 3], HasCheckedCertificate 16 8 ([[], [], [1, 1, 1, 2, 3]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k16t8p200, Certificates.k16t8p200_check⟩

private theorem k16t8_cover359 : ∀ P ∈ pathPatterns 1 2 [1, 1, 1, 3], HasCheckedCertificate 16 8 ([[], [], [1, 1, 1, 3]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [1, 1, 1, 3] [] ∧ LexLE [] [])) h)

private theorem k16t8_cover360 : ∀ P ∈ pathPatterns 0 1 [1, 1, 1, 3, 1], HasCheckedCertificate 16 8 ([[], [], [1, 1, 1, 3, 1]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k16t8p201, Certificates.k16t8p201_check⟩

private theorem k16t8_cover361 : ∀ P ∈ pathPatterns 0 0 [1, 1, 1, 3, 2], HasCheckedCertificate 16 8 ([[], [], [1, 1, 1, 3, 2]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k16t8p202, Certificates.k16t8p202_check⟩

private theorem k16t8_cover362 : ∀ P ∈ pathPatterns 1 1 [1, 1, 1, 4], HasCheckedCertificate 16 8 ([[], [], [1, 1, 1, 4]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [1, 1, 1, 4] [] ∧ LexLE [] [])) h)

private theorem k16t8_cover363 : ∀ P ∈ pathPatterns 0 0 [1, 1, 1, 4, 1], HasCheckedCertificate 16 8 ([[], [], [1, 1, 1, 4, 1]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k16t8p203, Certificates.k16t8p203_check⟩

private theorem k16t8_cover364 : ∀ P ∈ pathPatterns 1 0 [1, 1, 1, 5], HasCheckedCertificate 16 8 ([[], [], [1, 1, 1, 5]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [1, 1, 1, 5] [] ∧ LexLE [] [])) h)

private theorem k16t8_cover366 : ∀ P ∈ pathPatterns 0 2 [2], HasCheckedCertificate 16 8 ([[], [], [1, 1, 2], [2]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k16t8p204, Certificates.k16t8p204_check⟩

private theorem k16t8_cover367 : ∀ P ∈ pathPatterns 0 1 [3], HasCheckedCertificate 16 8 ([[], [], [1, 1, 2], [3]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k16t8p205, Certificates.k16t8p205_check⟩

private theorem k16t8_cover368 : ∀ P ∈ pathPatterns 0 0 [4], HasCheckedCertificate 16 8 ([[], [], [1, 1, 2], [4]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k16t8p206, Certificates.k16t8p206_check⟩

private theorem k16t8_cover365 : ∀ P ∈ pathPatterns 2 4 [1, 1, 2], HasCheckedCertificate 16 8 ([[], [], [1, 1, 2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [1, 1, 2] [] ∧ LexLE [] [])) h)
      · intro q
        fin_cases q
        · exact by
            intro h
            exact False.elim ((by decide : ¬ (LexLE [1, 1, 2] [1] ∧ LexLE [1] [1])) h)
        · exact by
            intro _
            exact k16t8_cover366
        · exact by
            intro _
            exact k16t8_cover367
        · exact by
            intro _
            exact k16t8_cover368

private theorem k16t8_cover369 : ∀ P ∈ pathPatterns 1 3 [1, 1, 2, 1], HasCheckedCertificate 16 8 ([[], [], [1, 1, 2, 1]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [1, 1, 2, 1] [] ∧ LexLE [] [])) h)

private theorem k16t8_cover370 : ∀ P ∈ pathPatterns 0 2 [1, 1, 2, 1, 1], HasCheckedCertificate 16 8 ([[], [], [1, 1, 2, 1, 1]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k16t8p207, Certificates.k16t8p207_check⟩

private theorem k16t8_cover371 : ∀ P ∈ pathPatterns 0 1 [1, 1, 2, 1, 2], HasCheckedCertificate 16 8 ([[], [], [1, 1, 2, 1, 2]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k16t8p208, Certificates.k16t8p208_check⟩

private theorem k16t8_cover372 : ∀ P ∈ pathPatterns 0 0 [1, 1, 2, 1, 3], HasCheckedCertificate 16 8 ([[], [], [1, 1, 2, 1, 3]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k16t8p209, Certificates.k16t8p209_check⟩

private theorem k16t8_cover373 : ∀ P ∈ pathPatterns 1 2 [1, 1, 2, 2], HasCheckedCertificate 16 8 ([[], [], [1, 1, 2, 2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [1, 1, 2, 2] [] ∧ LexLE [] [])) h)

private theorem k16t8_cover374 : ∀ P ∈ pathPatterns 0 1 [1, 1, 2, 2, 1], HasCheckedCertificate 16 8 ([[], [], [1, 1, 2, 2, 1]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k16t8p210, Certificates.k16t8p210_check⟩

private theorem k16t8_cover375 : ∀ P ∈ pathPatterns 0 0 [1, 1, 2, 2, 2], HasCheckedCertificate 16 8 ([[], [], [1, 1, 2, 2, 2]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k16t8p211, Certificates.k16t8p211_check⟩

private theorem k16t8_cover376 : ∀ P ∈ pathPatterns 1 1 [1, 1, 2, 3], HasCheckedCertificate 16 8 ([[], [], [1, 1, 2, 3]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [1, 1, 2, 3] [] ∧ LexLE [] [])) h)

private theorem k16t8_cover377 : ∀ P ∈ pathPatterns 0 0 [1, 1, 2, 3, 1], HasCheckedCertificate 16 8 ([[], [], [1, 1, 2, 3, 1]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k16t8p212, Certificates.k16t8p212_check⟩

private theorem k16t8_cover378 : ∀ P ∈ pathPatterns 1 0 [1, 1, 2, 4], HasCheckedCertificate 16 8 ([[], [], [1, 1, 2, 4]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [1, 1, 2, 4] [] ∧ LexLE [] [])) h)

private theorem k16t8_cover380 : ∀ P ∈ pathPatterns 0 1 [2], HasCheckedCertificate 16 8 ([[], [], [1, 1, 3], [2]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k16t8p213, Certificates.k16t8p213_check⟩

private theorem k16t8_cover381 : ∀ P ∈ pathPatterns 0 0 [3], HasCheckedCertificate 16 8 ([[], [], [1, 1, 3], [3]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k16t8p214, Certificates.k16t8p214_check⟩

private theorem k16t8_cover379 : ∀ P ∈ pathPatterns 2 3 [1, 1, 3], HasCheckedCertificate 16 8 ([[], [], [1, 1, 3]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [1, 1, 3] [] ∧ LexLE [] [])) h)
      · intro q
        fin_cases q
        · exact by
            intro h
            exact False.elim ((by decide : ¬ (LexLE [1, 1, 3] [1] ∧ LexLE [1] [1])) h)
        · exact by
            intro _
            exact k16t8_cover380
        · exact by
            intro _
            exact k16t8_cover381

private theorem k16t8_cover382 : ∀ P ∈ pathPatterns 1 2 [1, 1, 3, 1], HasCheckedCertificate 16 8 ([[], [], [1, 1, 3, 1]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [1, 1, 3, 1] [] ∧ LexLE [] [])) h)

private theorem k16t8_cover383 : ∀ P ∈ pathPatterns 0 1 [1, 1, 3, 1, 1], HasCheckedCertificate 16 8 ([[], [], [1, 1, 3, 1, 1]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k16t8p215, Certificates.k16t8p215_check⟩

private theorem k16t8_cover384 : ∀ P ∈ pathPatterns 0 0 [1, 1, 3, 1, 2], HasCheckedCertificate 16 8 ([[], [], [1, 1, 3, 1, 2]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k16t8p216, Certificates.k16t8p216_check⟩

private theorem k16t8_cover385 : ∀ P ∈ pathPatterns 1 1 [1, 1, 3, 2], HasCheckedCertificate 16 8 ([[], [], [1, 1, 3, 2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [1, 1, 3, 2] [] ∧ LexLE [] [])) h)

private theorem k16t8_cover386 : ∀ P ∈ pathPatterns 0 0 [1, 1, 3, 2, 1], HasCheckedCertificate 16 8 ([[], [], [1, 1, 3, 2, 1]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k16t8p217, Certificates.k16t8p217_check⟩

private theorem k16t8_cover387 : ∀ P ∈ pathPatterns 1 0 [1, 1, 3, 3], HasCheckedCertificate 16 8 ([[], [], [1, 1, 3, 3]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [1, 1, 3, 3] [] ∧ LexLE [] [])) h)

private theorem k16t8_cover389 : ∀ P ∈ pathPatterns 0 0 [2], HasCheckedCertificate 16 8 ([[], [], [1, 1, 4], [2]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k16t8p218, Certificates.k16t8p218_check⟩

private theorem k16t8_cover388 : ∀ P ∈ pathPatterns 2 2 [1, 1, 4], HasCheckedCertificate 16 8 ([[], [], [1, 1, 4]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [1, 1, 4] [] ∧ LexLE [] [])) h)
      · intro q
        fin_cases q
        · exact by
            intro h
            exact False.elim ((by decide : ¬ (LexLE [1, 1, 4] [1] ∧ LexLE [1] [1])) h)
        · exact by
            intro _
            exact k16t8_cover389

private theorem k16t8_cover390 : ∀ P ∈ pathPatterns 1 1 [1, 1, 4, 1], HasCheckedCertificate 16 8 ([[], [], [1, 1, 4, 1]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [1, 1, 4, 1] [] ∧ LexLE [] [])) h)

private theorem k16t8_cover391 : ∀ P ∈ pathPatterns 0 0 [1, 1, 4, 1, 1], HasCheckedCertificate 16 8 ([[], [], [1, 1, 4, 1, 1]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k16t8p219, Certificates.k16t8p219_check⟩

private theorem k16t8_cover392 : ∀ P ∈ pathPatterns 1 0 [1, 1, 4, 2], HasCheckedCertificate 16 8 ([[], [], [1, 1, 4, 2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [1, 1, 4, 2] [] ∧ LexLE [] [])) h)

private theorem k16t8_cover393 : ∀ P ∈ pathPatterns 2 1 [1, 1, 5], HasCheckedCertificate 16 8 ([[], [], [1, 1, 5]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [1, 1, 5] [] ∧ LexLE [] [])) h)
      · intro q
        fin_cases q
        · exact by
            intro h
            exact False.elim ((by decide : ¬ (LexLE [1, 1, 5] [1] ∧ LexLE [1] [1])) h)

private theorem k16t8_cover394 : ∀ P ∈ pathPatterns 1 0 [1, 1, 5, 1], HasCheckedCertificate 16 8 ([[], [], [1, 1, 5, 1]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [1, 1, 5, 1] [] ∧ LexLE [] [])) h)

private theorem k16t8_cover395 : ∀ P ∈ pathPatterns 2 0 [1, 1, 6], HasCheckedCertificate 16 8 ([[], [], [1, 1, 6]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [1, 1, 6] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k16t8_seq329 : amountSequenceForall 3 6 (fun tail =>
    (LexLE [] ([1, 1] ++ tail) ∧ LexLE ([1, 1] ++ tail) ([1, 1] ++ tail).reverse) →
    ∀ P ∈ pathPatterns (5 - ([1, 1] ++ tail).length) (8 - ([1, 1] ++ tail).sum) ([1, 1] ++ tail),
      HasCheckedCertificate 16 8 ([[], []] ++ (([1, 1] ++ tail) :: P))) :=
by
  constructor
  · exact by
      intro _
      exact k16t8_cover330
  · intro q
    fin_cases q
    · exact by
        constructor
        · exact by
            intro _
            exact k16t8_cover345
        · intro q
          fin_cases q
          · exact by
              constructor
              · exact by
                  intro _
                  exact k16t8_cover350
              · intro q
                fin_cases q
                · exact by
                    intro _
                    exact k16t8_cover351
                · exact by
                    intro _
                    exact k16t8_cover352
                · exact by
                    intro _
                    exact k16t8_cover353
                · exact by
                    intro _
                    exact k16t8_cover354
          · exact by
              constructor
              · exact by
                  intro _
                  exact k16t8_cover355
              · intro q
                fin_cases q
                · exact by
                    intro _
                    exact k16t8_cover356
                · exact by
                    intro _
                    exact k16t8_cover357
                · exact by
                    intro _
                    exact k16t8_cover358
          · exact by
              constructor
              · exact by
                  intro _
                  exact k16t8_cover359
              · intro q
                fin_cases q
                · exact by
                    intro _
                    exact k16t8_cover360
                · exact by
                    intro _
                    exact k16t8_cover361
          · exact by
              constructor
              · exact by
                  intro _
                  exact k16t8_cover362
              · intro q
                fin_cases q
                · exact by
                    intro _
                    exact k16t8_cover363
          · exact by
              constructor
              · exact by
                  intro _
                  exact k16t8_cover364
              · intro q
                exact Fin.elim0 q
    · exact by
        constructor
        · exact by
            intro _
            exact k16t8_cover365
        · intro q
          fin_cases q
          · exact by
              constructor
              · exact by
                  intro _
                  exact k16t8_cover369
              · intro q
                fin_cases q
                · exact by
                    intro _
                    exact k16t8_cover370
                · exact by
                    intro _
                    exact k16t8_cover371
                · exact by
                    intro _
                    exact k16t8_cover372
          · exact by
              constructor
              · exact by
                  intro _
                  exact k16t8_cover373
              · intro q
                fin_cases q
                · exact by
                    intro _
                    exact k16t8_cover374
                · exact by
                    intro _
                    exact k16t8_cover375
          · exact by
              constructor
              · exact by
                  intro _
                  exact k16t8_cover376
              · intro q
                fin_cases q
                · exact by
                    intro _
                    exact k16t8_cover377
          · exact by
              constructor
              · exact by
                  intro _
                  exact k16t8_cover378
              · intro q
                exact Fin.elim0 q
    · exact by
        constructor
        · exact by
            intro _
            exact k16t8_cover379
        · intro q
          fin_cases q
          · exact by
              constructor
              · exact by
                  intro _
                  exact k16t8_cover382
              · intro q
                fin_cases q
                · exact by
                    intro _
                    exact k16t8_cover383
                · exact by
                    intro _
                    exact k16t8_cover384
          · exact by
              constructor
              · exact by
                  intro _
                  exact k16t8_cover385
              · intro q
                fin_cases q
                · exact by
                    intro _
                    exact k16t8_cover386
          · exact by
              constructor
              · exact by
                  intro _
                  exact k16t8_cover387
              · intro q
                exact Fin.elim0 q
    · exact by
        constructor
        · exact by
            intro _
            exact k16t8_cover388
        · intro q
          fin_cases q
          · exact by
              constructor
              · exact by
                  intro _
                  exact k16t8_cover390
              · intro q
                fin_cases q
                · exact by
                    intro _
                    exact k16t8_cover391
          · exact by
              constructor
              · exact by
                  intro _
                  exact k16t8_cover392
              · intro q
                exact Fin.elim0 q
    · exact by
        constructor
        · exact by
            intro _
            exact k16t8_cover393
        · intro q
          fin_cases q
          · exact by
              constructor
              · exact by
                  intro _
                  exact k16t8_cover394
              · intro q
                exact Fin.elim0 q
    · exact by
        constructor
        · exact by
            intro _
            exact k16t8_cover395
        · intro q
          exact Fin.elim0 q

private theorem k16t8_cover398 : ∀ P ∈ pathPatterns 0 2 [1, 2], HasCheckedCertificate 16 8 ([[], [], [1, 2], [1, 2]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k16t8p220, Certificates.k16t8p220_check⟩

private theorem k16t8_cover399 : ∀ P ∈ pathPatterns 0 1 [1, 3], HasCheckedCertificate 16 8 ([[], [], [1, 2], [1, 3]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k16t8p221, Certificates.k16t8p221_check⟩

private theorem k16t8_cover400 : ∀ P ∈ pathPatterns 0 0 [1, 4], HasCheckedCertificate 16 8 ([[], [], [1, 2], [1, 4]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k16t8p222, Certificates.k16t8p222_check⟩

private theorem k16t8_cover401 : ∀ P ∈ pathPatterns 1 3 [2], HasCheckedCertificate 16 8 ([[], [], [1, 2], [2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [2] [] ∧ LexLE [] [])) h)

private theorem k16t8_cover402 : ∀ P ∈ pathPatterns 0 1 [2, 2], HasCheckedCertificate 16 8 ([[], [], [1, 2], [2, 2]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k16t8p223, Certificates.k16t8p223_check⟩

private theorem k16t8_cover403 : ∀ P ∈ pathPatterns 0 0 [2, 3], HasCheckedCertificate 16 8 ([[], [], [1, 2], [2, 3]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k16t8p224, Certificates.k16t8p224_check⟩

private theorem k16t8_cover404 : ∀ P ∈ pathPatterns 1 2 [3], HasCheckedCertificate 16 8 ([[], [], [1, 2], [3]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [3] [] ∧ LexLE [] [])) h)

private theorem k16t8_cover405 : ∀ P ∈ pathPatterns 1 1 [4], HasCheckedCertificate 16 8 ([[], [], [1, 2], [4]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [4] [] ∧ LexLE [] [])) h)

private theorem k16t8_cover406 : ∀ P ∈ pathPatterns 1 0 [5], HasCheckedCertificate 16 8 ([[], [], [1, 2], [5]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [5] [] ∧ LexLE [] [])) h)

private theorem k16t8_cover397 : ∀ P ∈ pathPatterns 3 5 [1, 2], HasCheckedCertificate 16 8 ([[], [], [1, 2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [1, 2] [] ∧ LexLE [] [])) h)
      · intro q
        fin_cases q
        · exact by
            constructor
            · exact by
                intro h
                exact False.elim ((by decide : ¬ (LexLE [1, 2] [1] ∧ LexLE [1] [1])) h)
            · intro q
              fin_cases q
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [1, 2] [1, 1] ∧ LexLE [1, 1] [1, 1])) h)
              · exact by
                  intro _
                  exact k16t8_cover398
              · exact by
                  intro _
                  exact k16t8_cover399
              · exact by
                  intro _
                  exact k16t8_cover400
        · exact by
            constructor
            · exact by
                intro _
                exact k16t8_cover401
            · intro q
              fin_cases q
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [1, 2] [2, 1] ∧ LexLE [2, 1] [1, 2])) h)
              · exact by
                  intro _
                  exact k16t8_cover402
              · exact by
                  intro _
                  exact k16t8_cover403
        · exact by
            constructor
            · exact by
                intro _
                exact k16t8_cover404
            · intro q
              fin_cases q
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [1, 2] [3, 1] ∧ LexLE [3, 1] [1, 3])) h)
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [1, 2] [3, 2] ∧ LexLE [3, 2] [2, 3])) h)
        · exact by
            constructor
            · exact by
                intro _
                exact k16t8_cover405
            · intro q
              fin_cases q
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [1, 2] [4, 1] ∧ LexLE [4, 1] [1, 4])) h)
        · exact by
            constructor
            · exact by
                intro _
                exact k16t8_cover406
            · intro q
              exact Fin.elim0 q

private theorem k16t8_cover408 : ∀ P ∈ pathPatterns 0 2 [2], HasCheckedCertificate 16 8 ([[], [], [1, 2, 1], [2]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k16t8p225, Certificates.k16t8p225_check⟩

private theorem k16t8_cover409 : ∀ P ∈ pathPatterns 0 1 [3], HasCheckedCertificate 16 8 ([[], [], [1, 2, 1], [3]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k16t8p226, Certificates.k16t8p226_check⟩

private theorem k16t8_cover410 : ∀ P ∈ pathPatterns 0 0 [4], HasCheckedCertificate 16 8 ([[], [], [1, 2, 1], [4]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k16t8p227, Certificates.k16t8p227_check⟩

private theorem k16t8_cover407 : ∀ P ∈ pathPatterns 2 4 [1, 2, 1], HasCheckedCertificate 16 8 ([[], [], [1, 2, 1]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [1, 2, 1] [] ∧ LexLE [] [])) h)
      · intro q
        fin_cases q
        · exact by
            intro h
            exact False.elim ((by decide : ¬ (LexLE [1, 2, 1] [1] ∧ LexLE [1] [1])) h)
        · exact by
            intro _
            exact k16t8_cover408
        · exact by
            intro _
            exact k16t8_cover409
        · exact by
            intro _
            exact k16t8_cover410

private theorem k16t8_cover411 : ∀ P ∈ pathPatterns 0 1 [1, 2, 1, 1, 2], HasCheckedCertificate 16 8 ([[], [], [1, 2, 1, 1, 2]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k16t8p228, Certificates.k16t8p228_check⟩

private theorem k16t8_cover412 : ∀ P ∈ pathPatterns 0 0 [1, 2, 1, 1, 3], HasCheckedCertificate 16 8 ([[], [], [1, 2, 1, 1, 3]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k16t8p229, Certificates.k16t8p229_check⟩

private theorem k16t8_cover413 : ∀ P ∈ pathPatterns 1 2 [1, 2, 1, 2], HasCheckedCertificate 16 8 ([[], [], [1, 2, 1, 2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [1, 2, 1, 2] [] ∧ LexLE [] [])) h)

private theorem k16t8_cover414 : ∀ P ∈ pathPatterns 0 1 [1, 2, 1, 2, 1], HasCheckedCertificate 16 8 ([[], [], [1, 2, 1, 2, 1]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k16t8p230, Certificates.k16t8p230_check⟩

private theorem k16t8_cover415 : ∀ P ∈ pathPatterns 0 0 [1, 2, 1, 2, 2], HasCheckedCertificate 16 8 ([[], [], [1, 2, 1, 2, 2]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k16t8p231, Certificates.k16t8p231_check⟩

private theorem k16t8_cover416 : ∀ P ∈ pathPatterns 1 1 [1, 2, 1, 3], HasCheckedCertificate 16 8 ([[], [], [1, 2, 1, 3]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [1, 2, 1, 3] [] ∧ LexLE [] [])) h)

private theorem k16t8_cover417 : ∀ P ∈ pathPatterns 0 0 [1, 2, 1, 3, 1], HasCheckedCertificate 16 8 ([[], [], [1, 2, 1, 3, 1]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k16t8p232, Certificates.k16t8p232_check⟩

private theorem k16t8_cover418 : ∀ P ∈ pathPatterns 1 0 [1, 2, 1, 4], HasCheckedCertificate 16 8 ([[], [], [1, 2, 1, 4]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [1, 2, 1, 4] [] ∧ LexLE [] [])) h)

private theorem k16t8_cover420 : ∀ P ∈ pathPatterns 0 1 [2], HasCheckedCertificate 16 8 ([[], [], [1, 2, 2], [2]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k16t8p233, Certificates.k16t8p233_check⟩

private theorem k16t8_cover421 : ∀ P ∈ pathPatterns 0 0 [3], HasCheckedCertificate 16 8 ([[], [], [1, 2, 2], [3]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k16t8p234, Certificates.k16t8p234_check⟩

private theorem k16t8_cover419 : ∀ P ∈ pathPatterns 2 3 [1, 2, 2], HasCheckedCertificate 16 8 ([[], [], [1, 2, 2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [1, 2, 2] [] ∧ LexLE [] [])) h)
      · intro q
        fin_cases q
        · exact by
            intro h
            exact False.elim ((by decide : ¬ (LexLE [1, 2, 2] [1] ∧ LexLE [1] [1])) h)
        · exact by
            intro _
            exact k16t8_cover420
        · exact by
            intro _
            exact k16t8_cover421

private theorem k16t8_cover422 : ∀ P ∈ pathPatterns 1 2 [1, 2, 2, 1], HasCheckedCertificate 16 8 ([[], [], [1, 2, 2, 1]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [1, 2, 2, 1] [] ∧ LexLE [] [])) h)

private theorem k16t8_cover423 : ∀ P ∈ pathPatterns 0 0 [1, 2, 2, 1, 2], HasCheckedCertificate 16 8 ([[], [], [1, 2, 2, 1, 2]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k16t8p235, Certificates.k16t8p235_check⟩

private theorem k16t8_cover424 : ∀ P ∈ pathPatterns 1 1 [1, 2, 2, 2], HasCheckedCertificate 16 8 ([[], [], [1, 2, 2, 2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [1, 2, 2, 2] [] ∧ LexLE [] [])) h)

private theorem k16t8_cover425 : ∀ P ∈ pathPatterns 0 0 [1, 2, 2, 2, 1], HasCheckedCertificate 16 8 ([[], [], [1, 2, 2, 2, 1]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k16t8p236, Certificates.k16t8p236_check⟩

private theorem k16t8_cover426 : ∀ P ∈ pathPatterns 1 0 [1, 2, 2, 3], HasCheckedCertificate 16 8 ([[], [], [1, 2, 2, 3]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [1, 2, 2, 3] [] ∧ LexLE [] [])) h)

private theorem k16t8_cover428 : ∀ P ∈ pathPatterns 0 0 [2], HasCheckedCertificate 16 8 ([[], [], [1, 2, 3], [2]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k16t8p237, Certificates.k16t8p237_check⟩

private theorem k16t8_cover427 : ∀ P ∈ pathPatterns 2 2 [1, 2, 3], HasCheckedCertificate 16 8 ([[], [], [1, 2, 3]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [1, 2, 3] [] ∧ LexLE [] [])) h)
      · intro q
        fin_cases q
        · exact by
            intro h
            exact False.elim ((by decide : ¬ (LexLE [1, 2, 3] [1] ∧ LexLE [1] [1])) h)
        · exact by
            intro _
            exact k16t8_cover428

private theorem k16t8_cover429 : ∀ P ∈ pathPatterns 1 1 [1, 2, 3, 1], HasCheckedCertificate 16 8 ([[], [], [1, 2, 3, 1]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [1, 2, 3, 1] [] ∧ LexLE [] [])) h)

private theorem k16t8_cover430 : ∀ P ∈ pathPatterns 1 0 [1, 2, 3, 2], HasCheckedCertificate 16 8 ([[], [], [1, 2, 3, 2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [1, 2, 3, 2] [] ∧ LexLE [] [])) h)

private theorem k16t8_cover431 : ∀ P ∈ pathPatterns 2 1 [1, 2, 4], HasCheckedCertificate 16 8 ([[], [], [1, 2, 4]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [1, 2, 4] [] ∧ LexLE [] [])) h)
      · intro q
        fin_cases q
        · exact by
            intro h
            exact False.elim ((by decide : ¬ (LexLE [1, 2, 4] [1] ∧ LexLE [1] [1])) h)

private theorem k16t8_cover432 : ∀ P ∈ pathPatterns 1 0 [1, 2, 4, 1], HasCheckedCertificate 16 8 ([[], [], [1, 2, 4, 1]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [1, 2, 4, 1] [] ∧ LexLE [] [])) h)

private theorem k16t8_cover433 : ∀ P ∈ pathPatterns 2 0 [1, 2, 5], HasCheckedCertificate 16 8 ([[], [], [1, 2, 5]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [1, 2, 5] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k16t8_seq396 : amountSequenceForall 3 5 (fun tail =>
    (LexLE [] ([1, 2] ++ tail) ∧ LexLE ([1, 2] ++ tail) ([1, 2] ++ tail).reverse) →
    ∀ P ∈ pathPatterns (5 - ([1, 2] ++ tail).length) (8 - ([1, 2] ++ tail).sum) ([1, 2] ++ tail),
      HasCheckedCertificate 16 8 ([[], []] ++ (([1, 2] ++ tail) :: P))) :=
by
  constructor
  · exact by
      intro _
      exact k16t8_cover397
  · intro q
    fin_cases q
    · exact by
        constructor
        · exact by
            intro _
            exact k16t8_cover407
        · intro q
          fin_cases q
          · exact by
              constructor
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [] [1, 2, 1, 1] ∧ LexLE [1, 2, 1, 1] [1, 1, 2, 1])) h)
              · intro q
                fin_cases q
                · exact by
                    intro h
                    exact False.elim ((by decide : ¬ (LexLE [] [1, 2, 1, 1, 1] ∧ LexLE [1, 2, 1, 1, 1] [1, 1, 1, 2, 1])) h)
                · exact by
                    intro _
                    exact k16t8_cover411
                · exact by
                    intro _
                    exact k16t8_cover412
          · exact by
              constructor
              · exact by
                  intro _
                  exact k16t8_cover413
              · intro q
                fin_cases q
                · exact by
                    intro _
                    exact k16t8_cover414
                · exact by
                    intro _
                    exact k16t8_cover415
          · exact by
              constructor
              · exact by
                  intro _
                  exact k16t8_cover416
              · intro q
                fin_cases q
                · exact by
                    intro _
                    exact k16t8_cover417
          · exact by
              constructor
              · exact by
                  intro _
                  exact k16t8_cover418
              · intro q
                exact Fin.elim0 q
    · exact by
        constructor
        · exact by
            intro _
            exact k16t8_cover419
        · intro q
          fin_cases q
          · exact by
              constructor
              · exact by
                  intro _
                  exact k16t8_cover422
              · intro q
                fin_cases q
                · exact by
                    intro h
                    exact False.elim ((by decide : ¬ (LexLE [] [1, 2, 2, 1, 1] ∧ LexLE [1, 2, 2, 1, 1] [1, 1, 2, 2, 1])) h)
                · exact by
                    intro _
                    exact k16t8_cover423
          · exact by
              constructor
              · exact by
                  intro _
                  exact k16t8_cover424
              · intro q
                fin_cases q
                · exact by
                    intro _
                    exact k16t8_cover425
          · exact by
              constructor
              · exact by
                  intro _
                  exact k16t8_cover426
              · intro q
                exact Fin.elim0 q
    · exact by
        constructor
        · exact by
            intro _
            exact k16t8_cover427
        · intro q
          fin_cases q
          · exact by
              constructor
              · exact by
                  intro _
                  exact k16t8_cover429
              · intro q
                fin_cases q
                · exact by
                    intro h
                    exact False.elim ((by decide : ¬ (LexLE [] [1, 2, 3, 1, 1] ∧ LexLE [1, 2, 3, 1, 1] [1, 1, 3, 2, 1])) h)
          · exact by
              constructor
              · exact by
                  intro _
                  exact k16t8_cover430
              · intro q
                exact Fin.elim0 q
    · exact by
        constructor
        · exact by
            intro _
            exact k16t8_cover431
        · intro q
          fin_cases q
          · exact by
              constructor
              · exact by
                  intro _
                  exact k16t8_cover432
              · intro q
                exact Fin.elim0 q
    · exact by
        constructor
        · exact by
            intro _
            exact k16t8_cover433
        · intro q
          exact Fin.elim0 q

private theorem k16t8_cover435 : ∀ P ∈ pathPatterns 0 0 [1, 3], HasCheckedCertificate 16 8 ([[], [], [1, 3], [1, 3]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k16t8p238, Certificates.k16t8p238_check⟩

private theorem k16t8_cover436 : ∀ P ∈ pathPatterns 1 2 [2], HasCheckedCertificate 16 8 ([[], [], [1, 3], [2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [2] [] ∧ LexLE [] [])) h)

private theorem k16t8_cover437 : ∀ P ∈ pathPatterns 0 0 [2, 2], HasCheckedCertificate 16 8 ([[], [], [1, 3], [2, 2]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k16t8p239, Certificates.k16t8p239_check⟩

private theorem k16t8_cover438 : ∀ P ∈ pathPatterns 1 1 [3], HasCheckedCertificate 16 8 ([[], [], [1, 3], [3]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [3] [] ∧ LexLE [] [])) h)

private theorem k16t8_cover439 : ∀ P ∈ pathPatterns 1 0 [4], HasCheckedCertificate 16 8 ([[], [], [1, 3], [4]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [4] [] ∧ LexLE [] [])) h)

private theorem k16t8_cover434 : ∀ P ∈ pathPatterns 3 4 [1, 3], HasCheckedCertificate 16 8 ([[], [], [1, 3]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [1, 3] [] ∧ LexLE [] [])) h)
      · intro q
        fin_cases q
        · exact by
            constructor
            · exact by
                intro h
                exact False.elim ((by decide : ¬ (LexLE [1, 3] [1] ∧ LexLE [1] [1])) h)
            · intro q
              fin_cases q
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [1, 3] [1, 1] ∧ LexLE [1, 1] [1, 1])) h)
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [1, 3] [1, 2] ∧ LexLE [1, 2] [2, 1])) h)
              · exact by
                  intro _
                  exact k16t8_cover435
        · exact by
            constructor
            · exact by
                intro _
                exact k16t8_cover436
            · intro q
              fin_cases q
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [1, 3] [2, 1] ∧ LexLE [2, 1] [1, 2])) h)
              · exact by
                  intro _
                  exact k16t8_cover437
        · exact by
            constructor
            · exact by
                intro _
                exact k16t8_cover438
            · intro q
              fin_cases q
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [1, 3] [3, 1] ∧ LexLE [3, 1] [1, 3])) h)
        · exact by
            constructor
            · exact by
                intro _
                exact k16t8_cover439
            · intro q
              exact Fin.elim0 q

private theorem k16t8_cover441 : ∀ P ∈ pathPatterns 0 1 [2], HasCheckedCertificate 16 8 ([[], [], [1, 3, 1], [2]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k16t8p240, Certificates.k16t8p240_check⟩

private theorem k16t8_cover442 : ∀ P ∈ pathPatterns 0 0 [3], HasCheckedCertificate 16 8 ([[], [], [1, 3, 1], [3]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k16t8p241, Certificates.k16t8p241_check⟩

private theorem k16t8_cover440 : ∀ P ∈ pathPatterns 2 3 [1, 3, 1], HasCheckedCertificate 16 8 ([[], [], [1, 3, 1]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [1, 3, 1] [] ∧ LexLE [] [])) h)
      · intro q
        fin_cases q
        · exact by
            intro h
            exact False.elim ((by decide : ¬ (LexLE [1, 3, 1] [1] ∧ LexLE [1] [1])) h)
        · exact by
            intro _
            exact k16t8_cover441
        · exact by
            intro _
            exact k16t8_cover442

private theorem k16t8_cover443 : ∀ P ∈ pathPatterns 0 0 [1, 3, 1, 1, 2], HasCheckedCertificate 16 8 ([[], [], [1, 3, 1, 1, 2]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k16t8p242, Certificates.k16t8p242_check⟩

private theorem k16t8_cover444 : ∀ P ∈ pathPatterns 1 1 [1, 3, 1, 2], HasCheckedCertificate 16 8 ([[], [], [1, 3, 1, 2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [1, 3, 1, 2] [] ∧ LexLE [] [])) h)

private theorem k16t8_cover445 : ∀ P ∈ pathPatterns 1 0 [1, 3, 1, 3], HasCheckedCertificate 16 8 ([[], [], [1, 3, 1, 3]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [1, 3, 1, 3] [] ∧ LexLE [] [])) h)

private theorem k16t8_cover447 : ∀ P ∈ pathPatterns 0 0 [2], HasCheckedCertificate 16 8 ([[], [], [1, 3, 2], [2]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k16t8p243, Certificates.k16t8p243_check⟩

private theorem k16t8_cover446 : ∀ P ∈ pathPatterns 2 2 [1, 3, 2], HasCheckedCertificate 16 8 ([[], [], [1, 3, 2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [1, 3, 2] [] ∧ LexLE [] [])) h)
      · intro q
        fin_cases q
        · exact by
            intro h
            exact False.elim ((by decide : ¬ (LexLE [1, 3, 2] [1] ∧ LexLE [1] [1])) h)
        · exact by
            intro _
            exact k16t8_cover447

private theorem k16t8_cover448 : ∀ P ∈ pathPatterns 1 0 [1, 3, 2, 2], HasCheckedCertificate 16 8 ([[], [], [1, 3, 2, 2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [1, 3, 2, 2] [] ∧ LexLE [] [])) h)

private theorem k16t8_cover449 : ∀ P ∈ pathPatterns 2 1 [1, 3, 3], HasCheckedCertificate 16 8 ([[], [], [1, 3, 3]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [1, 3, 3] [] ∧ LexLE [] [])) h)
      · intro q
        fin_cases q
        · exact by
            intro h
            exact False.elim ((by decide : ¬ (LexLE [1, 3, 3] [1] ∧ LexLE [1] [1])) h)

private theorem k16t8_cover450 : ∀ P ∈ pathPatterns 1 0 [1, 3, 3, 1], HasCheckedCertificate 16 8 ([[], [], [1, 3, 3, 1]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [1, 3, 3, 1] [] ∧ LexLE [] [])) h)

private theorem k16t8_cover451 : ∀ P ∈ pathPatterns 2 0 [1, 3, 4], HasCheckedCertificate 16 8 ([[], [], [1, 3, 4]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [1, 3, 4] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k16t8_cover453 : ∀ P ∈ pathPatterns 1 1 [2], HasCheckedCertificate 16 8 ([[], [], [1, 4], [2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [2] [] ∧ LexLE [] [])) h)

private theorem k16t8_cover454 : ∀ P ∈ pathPatterns 1 0 [3], HasCheckedCertificate 16 8 ([[], [], [1, 4], [3]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [3] [] ∧ LexLE [] [])) h)

private theorem k16t8_cover452 : ∀ P ∈ pathPatterns 3 3 [1, 4], HasCheckedCertificate 16 8 ([[], [], [1, 4]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [1, 4] [] ∧ LexLE [] [])) h)
      · intro q
        fin_cases q
        · exact by
            constructor
            · exact by
                intro h
                exact False.elim ((by decide : ¬ (LexLE [1, 4] [1] ∧ LexLE [1] [1])) h)
            · intro q
              fin_cases q
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [1, 4] [1, 1] ∧ LexLE [1, 1] [1, 1])) h)
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [1, 4] [1, 2] ∧ LexLE [1, 2] [2, 1])) h)
        · exact by
            constructor
            · exact by
                intro _
                exact k16t8_cover453
            · intro q
              fin_cases q
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [1, 4] [2, 1] ∧ LexLE [2, 1] [1, 2])) h)
        · exact by
            constructor
            · exact by
                intro _
                exact k16t8_cover454
            · intro q
              exact Fin.elim0 q

private theorem k16t8_cover456 : ∀ P ∈ pathPatterns 0 0 [2], HasCheckedCertificate 16 8 ([[], [], [1, 4, 1], [2]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k16t8p244, Certificates.k16t8p244_check⟩

private theorem k16t8_cover455 : ∀ P ∈ pathPatterns 2 2 [1, 4, 1], HasCheckedCertificate 16 8 ([[], [], [1, 4, 1]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [1, 4, 1] [] ∧ LexLE [] [])) h)
      · intro q
        fin_cases q
        · exact by
            intro h
            exact False.elim ((by decide : ¬ (LexLE [1, 4, 1] [1] ∧ LexLE [1] [1])) h)
        · exact by
            intro _
            exact k16t8_cover456

private theorem k16t8_cover457 : ∀ P ∈ pathPatterns 1 0 [1, 4, 1, 2], HasCheckedCertificate 16 8 ([[], [], [1, 4, 1, 2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [1, 4, 1, 2] [] ∧ LexLE [] [])) h)

private theorem k16t8_cover458 : ∀ P ∈ pathPatterns 2 1 [1, 4, 2], HasCheckedCertificate 16 8 ([[], [], [1, 4, 2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [1, 4, 2] [] ∧ LexLE [] [])) h)
      · intro q
        fin_cases q
        · exact by
            intro h
            exact False.elim ((by decide : ¬ (LexLE [1, 4, 2] [1] ∧ LexLE [1] [1])) h)

private theorem k16t8_cover459 : ∀ P ∈ pathPatterns 2 0 [1, 4, 3], HasCheckedCertificate 16 8 ([[], [], [1, 4, 3]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [1, 4, 3] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k16t8_cover461 : ∀ P ∈ pathPatterns 1 0 [2], HasCheckedCertificate 16 8 ([[], [], [1, 5], [2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [2] [] ∧ LexLE [] [])) h)

private theorem k16t8_cover460 : ∀ P ∈ pathPatterns 3 2 [1, 5], HasCheckedCertificate 16 8 ([[], [], [1, 5]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [1, 5] [] ∧ LexLE [] [])) h)
      · intro q
        fin_cases q
        · exact by
            constructor
            · exact by
                intro h
                exact False.elim ((by decide : ¬ (LexLE [1, 5] [1] ∧ LexLE [1] [1])) h)
            · intro q
              fin_cases q
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [1, 5] [1, 1] ∧ LexLE [1, 1] [1, 1])) h)
        · exact by
            constructor
            · exact by
                intro _
                exact k16t8_cover461
            · intro q
              exact Fin.elim0 q

private theorem k16t8_cover462 : ∀ P ∈ pathPatterns 2 1 [1, 5, 1], HasCheckedCertificate 16 8 ([[], [], [1, 5, 1]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [1, 5, 1] [] ∧ LexLE [] [])) h)
      · intro q
        fin_cases q
        · exact by
            intro h
            exact False.elim ((by decide : ¬ (LexLE [1, 5, 1] [1] ∧ LexLE [1] [1])) h)

private theorem k16t8_cover463 : ∀ P ∈ pathPatterns 2 0 [1, 5, 2], HasCheckedCertificate 16 8 ([[], [], [1, 5, 2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [1, 5, 2] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k16t8_cover464 : ∀ P ∈ pathPatterns 3 1 [1, 6], HasCheckedCertificate 16 8 ([[], [], [1, 6]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [1, 6] [] ∧ LexLE [] [])) h)
      · intro q
        fin_cases q
        · exact by
            constructor
            · exact by
                intro h
                exact False.elim ((by decide : ¬ (LexLE [1, 6] [1] ∧ LexLE [1] [1])) h)
            · intro q
              exact Fin.elim0 q

private theorem k16t8_cover465 : ∀ P ∈ pathPatterns 2 0 [1, 6, 1], HasCheckedCertificate 16 8 ([[], [], [1, 6, 1]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [1, 6, 1] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k16t8_cover466 : ∀ P ∈ pathPatterns 3 0 [1, 7], HasCheckedCertificate 16 8 ([[], [], [1, 7]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [1, 7] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k16t8_seq273 : amountSequenceForall 4 7 (fun tail =>
    (LexLE [] ([1] ++ tail) ∧ LexLE ([1] ++ tail) ([1] ++ tail).reverse) →
    ∀ P ∈ pathPatterns (5 - ([1] ++ tail).length) (8 - ([1] ++ tail).sum) ([1] ++ tail),
      HasCheckedCertificate 16 8 ([[], []] ++ (([1] ++ tail) :: P))) :=
by
  constructor
  · exact by
      intro _
      exact k16t8_cover274
  · intro q
    fin_cases q
    · exact k16t8_seq329

    · exact k16t8_seq396

    · exact by
        constructor
        · exact by
            intro _
            exact k16t8_cover434
        · intro q
          fin_cases q
          · exact by
              constructor
              · exact by
                  intro _
                  exact k16t8_cover440
              · intro q
                fin_cases q
                · exact by
                    constructor
                    · exact by
                        intro h
                        exact False.elim ((by decide : ¬ (LexLE [] [1, 3, 1, 1] ∧ LexLE [1, 3, 1, 1] [1, 1, 3, 1])) h)
                    · intro q
                      fin_cases q
                      · exact by
                          intro h
                          exact False.elim ((by decide : ¬ (LexLE [] [1, 3, 1, 1, 1] ∧ LexLE [1, 3, 1, 1, 1] [1, 1, 1, 3, 1])) h)
                      · exact by
                          intro _
                          exact k16t8_cover443
                · exact by
                    constructor
                    · exact by
                        intro _
                        exact k16t8_cover444
                    · intro q
                      fin_cases q
                      · exact by
                          intro h
                          exact False.elim ((by decide : ¬ (LexLE [] [1, 3, 1, 2, 1] ∧ LexLE [1, 3, 1, 2, 1] [1, 2, 1, 3, 1])) h)
                · exact by
                    constructor
                    · exact by
                        intro _
                        exact k16t8_cover445
                    · intro q
                      exact Fin.elim0 q
          · exact by
              constructor
              · exact by
                  intro _
                  exact k16t8_cover446
              · intro q
                fin_cases q
                · exact by
                    constructor
                    · exact by
                        intro h
                        exact False.elim ((by decide : ¬ (LexLE [] [1, 3, 2, 1] ∧ LexLE [1, 3, 2, 1] [1, 2, 3, 1])) h)
                    · intro q
                      fin_cases q
                      · exact by
                          intro h
                          exact False.elim ((by decide : ¬ (LexLE [] [1, 3, 2, 1, 1] ∧ LexLE [1, 3, 2, 1, 1] [1, 1, 2, 3, 1])) h)
                · exact by
                    constructor
                    · exact by
                        intro _
                        exact k16t8_cover448
                    · intro q
                      exact Fin.elim0 q
          · exact by
              constructor
              · exact by
                  intro _
                  exact k16t8_cover449
              · intro q
                fin_cases q
                · exact by
                    constructor
                    · exact by
                        intro _
                        exact k16t8_cover450
                    · intro q
                      exact Fin.elim0 q
          · exact by
              constructor
              · exact by
                  intro _
                  exact k16t8_cover451
              · intro q
                exact Fin.elim0 q
    · exact by
        constructor
        · exact by
            intro _
            exact k16t8_cover452
        · intro q
          fin_cases q
          · exact by
              constructor
              · exact by
                  intro _
                  exact k16t8_cover455
              · intro q
                fin_cases q
                · exact by
                    constructor
                    · exact by
                        intro h
                        exact False.elim ((by decide : ¬ (LexLE [] [1, 4, 1, 1] ∧ LexLE [1, 4, 1, 1] [1, 1, 4, 1])) h)
                    · intro q
                      fin_cases q
                      · exact by
                          intro h
                          exact False.elim ((by decide : ¬ (LexLE [] [1, 4, 1, 1, 1] ∧ LexLE [1, 4, 1, 1, 1] [1, 1, 1, 4, 1])) h)
                · exact by
                    constructor
                    · exact by
                        intro _
                        exact k16t8_cover457
                    · intro q
                      exact Fin.elim0 q
          · exact by
              constructor
              · exact by
                  intro _
                  exact k16t8_cover458
              · intro q
                fin_cases q
                · exact by
                    constructor
                    · exact by
                        intro h
                        exact False.elim ((by decide : ¬ (LexLE [] [1, 4, 2, 1] ∧ LexLE [1, 4, 2, 1] [1, 2, 4, 1])) h)
                    · intro q
                      exact Fin.elim0 q
          · exact by
              constructor
              · exact by
                  intro _
                  exact k16t8_cover459
              · intro q
                exact Fin.elim0 q
    · exact by
        constructor
        · exact by
            intro _
            exact k16t8_cover460
        · intro q
          fin_cases q
          · exact by
              constructor
              · exact by
                  intro _
                  exact k16t8_cover462
              · intro q
                fin_cases q
                · exact by
                    constructor
                    · exact by
                        intro h
                        exact False.elim ((by decide : ¬ (LexLE [] [1, 5, 1, 1] ∧ LexLE [1, 5, 1, 1] [1, 1, 5, 1])) h)
                    · intro q
                      exact Fin.elim0 q
          · exact by
              constructor
              · exact by
                  intro _
                  exact k16t8_cover463
              · intro q
                exact Fin.elim0 q
    · exact by
        constructor
        · exact by
            intro _
            exact k16t8_cover464
        · intro q
          fin_cases q
          · exact by
              constructor
              · exact by
                  intro _
                  exact k16t8_cover465
              · intro q
                exact Fin.elim0 q
    · exact by
        constructor
        · exact by
            intro _
            exact k16t8_cover466
        · intro q
          exact Fin.elim0 q

private theorem k16t8_cover471 : ∀ P ∈ pathPatterns 0 2 [2], HasCheckedCertificate 16 8 ([[], [], [2], [2], [2]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k16t8p245, Certificates.k16t8p245_check⟩

private theorem k16t8_cover472 : ∀ P ∈ pathPatterns 0 1 [3], HasCheckedCertificate 16 8 ([[], [], [2], [2], [3]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k16t8p246, Certificates.k16t8p246_check⟩

private theorem k16t8_cover473 : ∀ P ∈ pathPatterns 0 0 [4], HasCheckedCertificate 16 8 ([[], [], [2], [2], [4]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k16t8p247, Certificates.k16t8p247_check⟩

private theorem k16t8_cover470 : ∀ P ∈ pathPatterns 2 4 [2], HasCheckedCertificate 16 8 ([[], [], [2], [2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [2] [] ∧ LexLE [] [])) h)
      · intro q
        fin_cases q
        · exact by
            intro h
            exact False.elim ((by decide : ¬ (LexLE [2] [1] ∧ LexLE [1] [1])) h)
        · exact by
            intro _
            exact k16t8_cover471
        · exact by
            intro _
            exact k16t8_cover472
        · exact by
            intro _
            exact k16t8_cover473

private theorem k16t8_cover474 : ∀ P ∈ pathPatterns 0 1 [2, 1, 2], HasCheckedCertificate 16 8 ([[], [], [2], [2, 1, 2]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k16t8p248, Certificates.k16t8p248_check⟩

private theorem k16t8_cover475 : ∀ P ∈ pathPatterns 0 0 [2, 1, 3], HasCheckedCertificate 16 8 ([[], [], [2], [2, 1, 3]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k16t8p249, Certificates.k16t8p249_check⟩

private theorem k16t8_cover476 : ∀ P ∈ pathPatterns 1 2 [2, 2], HasCheckedCertificate 16 8 ([[], [], [2], [2, 2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [2, 2] [] ∧ LexLE [] [])) h)

private theorem k16t8_cover477 : ∀ P ∈ pathPatterns 0 0 [2, 2, 2], HasCheckedCertificate 16 8 ([[], [], [2], [2, 2, 2]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k16t8p250, Certificates.k16t8p250_check⟩

private theorem k16t8_cover478 : ∀ P ∈ pathPatterns 1 1 [2, 3], HasCheckedCertificate 16 8 ([[], [], [2], [2, 3]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [2, 3] [] ∧ LexLE [] [])) h)

private theorem k16t8_cover479 : ∀ P ∈ pathPatterns 1 0 [2, 4], HasCheckedCertificate 16 8 ([[], [], [2], [2, 4]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [2, 4] [] ∧ LexLE [] [])) h)

private theorem k16t8_cover481 : ∀ P ∈ pathPatterns 0 0 [3], HasCheckedCertificate 16 8 ([[], [], [2], [3], [3]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k16t8p251, Certificates.k16t8p251_check⟩

private theorem k16t8_cover480 : ∀ P ∈ pathPatterns 2 3 [3], HasCheckedCertificate 16 8 ([[], [], [2], [3]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [3] [] ∧ LexLE [] [])) h)
      · intro q
        fin_cases q
        · exact by
            intro h
            exact False.elim ((by decide : ¬ (LexLE [3] [1] ∧ LexLE [1] [1])) h)
        · exact by
            intro h
            exact False.elim ((by decide : ¬ (LexLE [3] [2] ∧ LexLE [2] [2])) h)
        · exact by
            intro _
            exact k16t8_cover481

private theorem k16t8_cover482 : ∀ P ∈ pathPatterns 1 0 [3, 3], HasCheckedCertificate 16 8 ([[], [], [2], [3, 3]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [3, 3] [] ∧ LexLE [] [])) h)

private theorem k16t8_cover483 : ∀ P ∈ pathPatterns 2 2 [4], HasCheckedCertificate 16 8 ([[], [], [2], [4]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [4] [] ∧ LexLE [] [])) h)
      · intro q
        fin_cases q
        · exact by
            intro h
            exact False.elim ((by decide : ¬ (LexLE [4] [1] ∧ LexLE [1] [1])) h)
        · exact by
            intro h
            exact False.elim ((by decide : ¬ (LexLE [4] [2] ∧ LexLE [2] [2])) h)

private theorem k16t8_cover484 : ∀ P ∈ pathPatterns 2 1 [5], HasCheckedCertificate 16 8 ([[], [], [2], [5]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [5] [] ∧ LexLE [] [])) h)
      · intro q
        fin_cases q
        · exact by
            intro h
            exact False.elim ((by decide : ¬ (LexLE [5] [1] ∧ LexLE [1] [1])) h)

private theorem k16t8_cover485 : ∀ P ∈ pathPatterns 2 0 [6], HasCheckedCertificate 16 8 ([[], [], [2], [6]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [6] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k16t8_seq469 : amountSequenceForall 3 6 (fun tail =>
    (LexLE [2] ([] ++ tail) ∧ LexLE ([] ++ tail) ([] ++ tail).reverse) →
    ∀ P ∈ pathPatterns (3 - ([] ++ tail).length) (6 - ([] ++ tail).sum) ([] ++ tail),
      HasCheckedCertificate 16 8 ([[], [], [2]] ++ (([] ++ tail) :: P))) :=
by
  constructor
  · exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [2] [] ∧ LexLE [] [])) h)
  · intro q
    fin_cases q
    · exact by
        constructor
        · exact by
            intro h
            exact False.elim ((by decide : ¬ (LexLE [2] [1] ∧ LexLE [1] [1])) h)
        · intro q
          fin_cases q
          · exact by
              constructor
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [2] [1, 1] ∧ LexLE [1, 1] [1, 1])) h)
              · intro q
                fin_cases q
                · exact by
                    intro h
                    exact False.elim ((by decide : ¬ (LexLE [2] [1, 1, 1] ∧ LexLE [1, 1, 1] [1, 1, 1])) h)
                · exact by
                    intro h
                    exact False.elim ((by decide : ¬ (LexLE [2] [1, 1, 2] ∧ LexLE [1, 1, 2] [2, 1, 1])) h)
                · exact by
                    intro h
                    exact False.elim ((by decide : ¬ (LexLE [2] [1, 1, 3] ∧ LexLE [1, 1, 3] [3, 1, 1])) h)
                · exact by
                    intro h
                    exact False.elim ((by decide : ¬ (LexLE [2] [1, 1, 4] ∧ LexLE [1, 1, 4] [4, 1, 1])) h)
          · exact by
              constructor
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [2] [1, 2] ∧ LexLE [1, 2] [2, 1])) h)
              · intro q
                fin_cases q
                · exact by
                    intro h
                    exact False.elim ((by decide : ¬ (LexLE [2] [1, 2, 1] ∧ LexLE [1, 2, 1] [1, 2, 1])) h)
                · exact by
                    intro h
                    exact False.elim ((by decide : ¬ (LexLE [2] [1, 2, 2] ∧ LexLE [1, 2, 2] [2, 2, 1])) h)
                · exact by
                    intro h
                    exact False.elim ((by decide : ¬ (LexLE [2] [1, 2, 3] ∧ LexLE [1, 2, 3] [3, 2, 1])) h)
          · exact by
              constructor
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [2] [1, 3] ∧ LexLE [1, 3] [3, 1])) h)
              · intro q
                fin_cases q
                · exact by
                    intro h
                    exact False.elim ((by decide : ¬ (LexLE [2] [1, 3, 1] ∧ LexLE [1, 3, 1] [1, 3, 1])) h)
                · exact by
                    intro h
                    exact False.elim ((by decide : ¬ (LexLE [2] [1, 3, 2] ∧ LexLE [1, 3, 2] [2, 3, 1])) h)
          · exact by
              constructor
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [2] [1, 4] ∧ LexLE [1, 4] [4, 1])) h)
              · intro q
                fin_cases q
                · exact by
                    intro h
                    exact False.elim ((by decide : ¬ (LexLE [2] [1, 4, 1] ∧ LexLE [1, 4, 1] [1, 4, 1])) h)
          · exact by
              constructor
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [2] [1, 5] ∧ LexLE [1, 5] [5, 1])) h)
              · intro q
                exact Fin.elim0 q
    · exact by
        constructor
        · exact by
            intro _
            exact k16t8_cover470
        · intro q
          fin_cases q
          · exact by
              constructor
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [2] [2, 1] ∧ LexLE [2, 1] [1, 2])) h)
              · intro q
                fin_cases q
                · exact by
                    intro h
                    exact False.elim ((by decide : ¬ (LexLE [2] [2, 1, 1] ∧ LexLE [2, 1, 1] [1, 1, 2])) h)
                · exact by
                    intro _
                    exact k16t8_cover474
                · exact by
                    intro _
                    exact k16t8_cover475
          · exact by
              constructor
              · exact by
                  intro _
                  exact k16t8_cover476
              · intro q
                fin_cases q
                · exact by
                    intro h
                    exact False.elim ((by decide : ¬ (LexLE [2] [2, 2, 1] ∧ LexLE [2, 2, 1] [1, 2, 2])) h)
                · exact by
                    intro _
                    exact k16t8_cover477
          · exact by
              constructor
              · exact by
                  intro _
                  exact k16t8_cover478
              · intro q
                fin_cases q
                · exact by
                    intro h
                    exact False.elim ((by decide : ¬ (LexLE [2] [2, 3, 1] ∧ LexLE [2, 3, 1] [1, 3, 2])) h)
          · exact by
              constructor
              · exact by
                  intro _
                  exact k16t8_cover479
              · intro q
                exact Fin.elim0 q
    · exact by
        constructor
        · exact by
            intro _
            exact k16t8_cover480
        · intro q
          fin_cases q
          · exact by
              constructor
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [2] [3, 1] ∧ LexLE [3, 1] [1, 3])) h)
              · intro q
                fin_cases q
                · exact by
                    intro h
                    exact False.elim ((by decide : ¬ (LexLE [2] [3, 1, 1] ∧ LexLE [3, 1, 1] [1, 1, 3])) h)
                · exact by
                    intro h
                    exact False.elim ((by decide : ¬ (LexLE [2] [3, 1, 2] ∧ LexLE [3, 1, 2] [2, 1, 3])) h)
          · exact by
              constructor
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [2] [3, 2] ∧ LexLE [3, 2] [2, 3])) h)
              · intro q
                fin_cases q
                · exact by
                    intro h
                    exact False.elim ((by decide : ¬ (LexLE [2] [3, 2, 1] ∧ LexLE [3, 2, 1] [1, 2, 3])) h)
          · exact by
              constructor
              · exact by
                  intro _
                  exact k16t8_cover482
              · intro q
                exact Fin.elim0 q
    · exact by
        constructor
        · exact by
            intro _
            exact k16t8_cover483
        · intro q
          fin_cases q
          · exact by
              constructor
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [2] [4, 1] ∧ LexLE [4, 1] [1, 4])) h)
              · intro q
                fin_cases q
                · exact by
                    intro h
                    exact False.elim ((by decide : ¬ (LexLE [2] [4, 1, 1] ∧ LexLE [4, 1, 1] [1, 1, 4])) h)
          · exact by
              constructor
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [2] [4, 2] ∧ LexLE [4, 2] [2, 4])) h)
              · intro q
                exact Fin.elim0 q
    · exact by
        constructor
        · exact by
            intro _
            exact k16t8_cover484
        · intro q
          fin_cases q
          · exact by
              constructor
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [2] [5, 1] ∧ LexLE [5, 1] [1, 5])) h)
              · intro q
                exact Fin.elim0 q
    · exact by
        constructor
        · exact by
            intro _
            exact k16t8_cover485
        · intro q
          exact Fin.elim0 q

private theorem k16t8_cover468 : ∀ P ∈ pathPatterns 4 6 [2], HasCheckedCertificate 16 8 ([[], [], [2]] ++ P) := by
  apply pathPatterns_forall_step
  exact k16t8_seq469


private theorem k16t8_cover487 : ∀ P ∈ pathPatterns 0 1 [2, 1, 1, 1, 2], HasCheckedCertificate 16 8 ([[], [], [2, 1, 1, 1, 2]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k16t8p252, Certificates.k16t8p252_check⟩

private theorem k16t8_cover488 : ∀ P ∈ pathPatterns 0 0 [2, 1, 1, 1, 3], HasCheckedCertificate 16 8 ([[], [], [2, 1, 1, 1, 3]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k16t8p253, Certificates.k16t8p253_check⟩

private theorem k16t8_cover489 : ∀ P ∈ pathPatterns 1 2 [2, 1, 1, 2], HasCheckedCertificate 16 8 ([[], [], [2, 1, 1, 2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [2, 1, 1, 2] [] ∧ LexLE [] [])) h)

private theorem k16t8_cover490 : ∀ P ∈ pathPatterns 0 0 [2, 1, 1, 2, 2], HasCheckedCertificate 16 8 ([[], [], [2, 1, 1, 2, 2]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k16t8p254, Certificates.k16t8p254_check⟩

private theorem k16t8_cover491 : ∀ P ∈ pathPatterns 1 1 [2, 1, 1, 3], HasCheckedCertificate 16 8 ([[], [], [2, 1, 1, 3]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [2, 1, 1, 3] [] ∧ LexLE [] [])) h)

private theorem k16t8_cover492 : ∀ P ∈ pathPatterns 1 0 [2, 1, 1, 4], HasCheckedCertificate 16 8 ([[], [], [2, 1, 1, 4]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [2, 1, 1, 4] [] ∧ LexLE [] [])) h)

private theorem k16t8_cover494 : ∀ P ∈ pathPatterns 0 0 [3], HasCheckedCertificate 16 8 ([[], [], [2, 1, 2], [3]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k16t8p255, Certificates.k16t8p255_check⟩

private theorem k16t8_cover493 : ∀ P ∈ pathPatterns 2 3 [2, 1, 2], HasCheckedCertificate 16 8 ([[], [], [2, 1, 2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [2, 1, 2] [] ∧ LexLE [] [])) h)
      · intro q
        fin_cases q
        · exact by
            intro h
            exact False.elim ((by decide : ¬ (LexLE [2, 1, 2] [1] ∧ LexLE [1] [1])) h)
        · exact by
            intro h
            exact False.elim ((by decide : ¬ (LexLE [2, 1, 2] [2] ∧ LexLE [2] [2])) h)
        · exact by
            intro _
            exact k16t8_cover494

private theorem k16t8_cover495 : ∀ P ∈ pathPatterns 0 0 [2, 1, 2, 1, 2], HasCheckedCertificate 16 8 ([[], [], [2, 1, 2, 1, 2]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k16t8p256, Certificates.k16t8p256_check⟩

private theorem k16t8_cover496 : ∀ P ∈ pathPatterns 1 1 [2, 1, 2, 2], HasCheckedCertificate 16 8 ([[], [], [2, 1, 2, 2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [2, 1, 2, 2] [] ∧ LexLE [] [])) h)

private theorem k16t8_cover497 : ∀ P ∈ pathPatterns 1 0 [2, 1, 2, 3], HasCheckedCertificate 16 8 ([[], [], [2, 1, 2, 3]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [2, 1, 2, 3] [] ∧ LexLE [] [])) h)

private theorem k16t8_cover498 : ∀ P ∈ pathPatterns 2 2 [2, 1, 3], HasCheckedCertificate 16 8 ([[], [], [2, 1, 3]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [2, 1, 3] [] ∧ LexLE [] [])) h)
      · intro q
        fin_cases q
        · exact by
            intro h
            exact False.elim ((by decide : ¬ (LexLE [2, 1, 3] [1] ∧ LexLE [1] [1])) h)
        · exact by
            intro h
            exact False.elim ((by decide : ¬ (LexLE [2, 1, 3] [2] ∧ LexLE [2] [2])) h)

private theorem k16t8_cover499 : ∀ P ∈ pathPatterns 1 0 [2, 1, 3, 2], HasCheckedCertificate 16 8 ([[], [], [2, 1, 3, 2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [2, 1, 3, 2] [] ∧ LexLE [] [])) h)

private theorem k16t8_cover500 : ∀ P ∈ pathPatterns 2 1 [2, 1, 4], HasCheckedCertificate 16 8 ([[], [], [2, 1, 4]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [2, 1, 4] [] ∧ LexLE [] [])) h)
      · intro q
        fin_cases q
        · exact by
            intro h
            exact False.elim ((by decide : ¬ (LexLE [2, 1, 4] [1] ∧ LexLE [1] [1])) h)

private theorem k16t8_cover501 : ∀ P ∈ pathPatterns 2 0 [2, 1, 5], HasCheckedCertificate 16 8 ([[], [], [2, 1, 5]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [2, 1, 5] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k16t8_seq486 : amountSequenceForall 3 5 (fun tail =>
    (LexLE [] ([2, 1] ++ tail) ∧ LexLE ([2, 1] ++ tail) ([2, 1] ++ tail).reverse) →
    ∀ P ∈ pathPatterns (5 - ([2, 1] ++ tail).length) (8 - ([2, 1] ++ tail).sum) ([2, 1] ++ tail),
      HasCheckedCertificate 16 8 ([[], []] ++ (([2, 1] ++ tail) :: P))) :=
by
  constructor
  · exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [] [2, 1] ∧ LexLE [2, 1] [1, 2])) h)
  · intro q
    fin_cases q
    · exact by
        constructor
        · exact by
            intro h
            exact False.elim ((by decide : ¬ (LexLE [] [2, 1, 1] ∧ LexLE [2, 1, 1] [1, 1, 2])) h)
        · intro q
          fin_cases q
          · exact by
              constructor
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [] [2, 1, 1, 1] ∧ LexLE [2, 1, 1, 1] [1, 1, 1, 2])) h)
              · intro q
                fin_cases q
                · exact by
                    intro h
                    exact False.elim ((by decide : ¬ (LexLE [] [2, 1, 1, 1, 1] ∧ LexLE [2, 1, 1, 1, 1] [1, 1, 1, 1, 2])) h)
                · exact by
                    intro _
                    exact k16t8_cover487
                · exact by
                    intro _
                    exact k16t8_cover488
          · exact by
              constructor
              · exact by
                  intro _
                  exact k16t8_cover489
              · intro q
                fin_cases q
                · exact by
                    intro h
                    exact False.elim ((by decide : ¬ (LexLE [] [2, 1, 1, 2, 1] ∧ LexLE [2, 1, 1, 2, 1] [1, 2, 1, 1, 2])) h)
                · exact by
                    intro _
                    exact k16t8_cover490
          · exact by
              constructor
              · exact by
                  intro _
                  exact k16t8_cover491
              · intro q
                fin_cases q
                · exact by
                    intro h
                    exact False.elim ((by decide : ¬ (LexLE [] [2, 1, 1, 3, 1] ∧ LexLE [2, 1, 1, 3, 1] [1, 3, 1, 1, 2])) h)
          · exact by
              constructor
              · exact by
                  intro _
                  exact k16t8_cover492
              · intro q
                exact Fin.elim0 q
    · exact by
        constructor
        · exact by
            intro _
            exact k16t8_cover493
        · intro q
          fin_cases q
          · exact by
              constructor
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [] [2, 1, 2, 1] ∧ LexLE [2, 1, 2, 1] [1, 2, 1, 2])) h)
              · intro q
                fin_cases q
                · exact by
                    intro h
                    exact False.elim ((by decide : ¬ (LexLE [] [2, 1, 2, 1, 1] ∧ LexLE [2, 1, 2, 1, 1] [1, 1, 2, 1, 2])) h)
                · exact by
                    intro _
                    exact k16t8_cover495
          · exact by
              constructor
              · exact by
                  intro _
                  exact k16t8_cover496
              · intro q
                fin_cases q
                · exact by
                    intro h
                    exact False.elim ((by decide : ¬ (LexLE [] [2, 1, 2, 2, 1] ∧ LexLE [2, 1, 2, 2, 1] [1, 2, 2, 1, 2])) h)
          · exact by
              constructor
              · exact by
                  intro _
                  exact k16t8_cover497
              · intro q
                exact Fin.elim0 q
    · exact by
        constructor
        · exact by
            intro _
            exact k16t8_cover498
        · intro q
          fin_cases q
          · exact by
              constructor
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [] [2, 1, 3, 1] ∧ LexLE [2, 1, 3, 1] [1, 3, 1, 2])) h)
              · intro q
                fin_cases q
                · exact by
                    intro h
                    exact False.elim ((by decide : ¬ (LexLE [] [2, 1, 3, 1, 1] ∧ LexLE [2, 1, 3, 1, 1] [1, 1, 3, 1, 2])) h)
          · exact by
              constructor
              · exact by
                  intro _
                  exact k16t8_cover499
              · intro q
                exact Fin.elim0 q
    · exact by
        constructor
        · exact by
            intro _
            exact k16t8_cover500
        · intro q
          fin_cases q
          · exact by
              constructor
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [] [2, 1, 4, 1] ∧ LexLE [2, 1, 4, 1] [1, 4, 1, 2])) h)
              · intro q
                exact Fin.elim0 q
    · exact by
        constructor
        · exact by
            intro _
            exact k16t8_cover501
        · intro q
          exact Fin.elim0 q

private theorem k16t8_cover503 : ∀ P ∈ pathPatterns 0 0 [2, 2], HasCheckedCertificate 16 8 ([[], [], [2, 2], [2, 2]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k16t8p257, Certificates.k16t8p257_check⟩

private theorem k16t8_cover504 : ∀ P ∈ pathPatterns 1 1 [3], HasCheckedCertificate 16 8 ([[], [], [2, 2], [3]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [3] [] ∧ LexLE [] [])) h)

private theorem k16t8_cover505 : ∀ P ∈ pathPatterns 1 0 [4], HasCheckedCertificate 16 8 ([[], [], [2, 2], [4]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [4] [] ∧ LexLE [] [])) h)

private theorem k16t8_cover502 : ∀ P ∈ pathPatterns 3 4 [2, 2], HasCheckedCertificate 16 8 ([[], [], [2, 2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [2, 2] [] ∧ LexLE [] [])) h)
      · intro q
        fin_cases q
        · exact by
            constructor
            · exact by
                intro h
                exact False.elim ((by decide : ¬ (LexLE [2, 2] [1] ∧ LexLE [1] [1])) h)
            · intro q
              fin_cases q
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [2, 2] [1, 1] ∧ LexLE [1, 1] [1, 1])) h)
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [2, 2] [1, 2] ∧ LexLE [1, 2] [2, 1])) h)
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [2, 2] [1, 3] ∧ LexLE [1, 3] [3, 1])) h)
        · exact by
            constructor
            · exact by
                intro h
                exact False.elim ((by decide : ¬ (LexLE [2, 2] [2] ∧ LexLE [2] [2])) h)
            · intro q
              fin_cases q
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [2, 2] [2, 1] ∧ LexLE [2, 1] [1, 2])) h)
              · exact by
                  intro _
                  exact k16t8_cover503
        · exact by
            constructor
            · exact by
                intro _
                exact k16t8_cover504
            · intro q
              fin_cases q
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [2, 2] [3, 1] ∧ LexLE [3, 1] [1, 3])) h)
        · exact by
            constructor
            · exact by
                intro _
                exact k16t8_cover505
            · intro q
              exact Fin.elim0 q

private theorem k16t8_cover506 : ∀ P ∈ pathPatterns 1 0 [2, 2, 1, 3], HasCheckedCertificate 16 8 ([[], [], [2, 2, 1, 3]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [2, 2, 1, 3] [] ∧ LexLE [] [])) h)

private theorem k16t8_cover507 : ∀ P ∈ pathPatterns 2 2 [2, 2, 2], HasCheckedCertificate 16 8 ([[], [], [2, 2, 2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [2, 2, 2] [] ∧ LexLE [] [])) h)
      · intro q
        fin_cases q
        · exact by
            intro h
            exact False.elim ((by decide : ¬ (LexLE [2, 2, 2] [1] ∧ LexLE [1] [1])) h)
        · exact by
            intro h
            exact False.elim ((by decide : ¬ (LexLE [2, 2, 2] [2] ∧ LexLE [2] [2])) h)

private theorem k16t8_cover508 : ∀ P ∈ pathPatterns 1 0 [2, 2, 2, 2], HasCheckedCertificate 16 8 ([[], [], [2, 2, 2, 2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [2, 2, 2, 2] [] ∧ LexLE [] [])) h)

private theorem k16t8_cover509 : ∀ P ∈ pathPatterns 2 1 [2, 2, 3], HasCheckedCertificate 16 8 ([[], [], [2, 2, 3]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [2, 2, 3] [] ∧ LexLE [] [])) h)
      · intro q
        fin_cases q
        · exact by
            intro h
            exact False.elim ((by decide : ¬ (LexLE [2, 2, 3] [1] ∧ LexLE [1] [1])) h)

private theorem k16t8_cover510 : ∀ P ∈ pathPatterns 2 0 [2, 2, 4], HasCheckedCertificate 16 8 ([[], [], [2, 2, 4]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [2, 2, 4] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k16t8_cover512 : ∀ P ∈ pathPatterns 1 0 [3], HasCheckedCertificate 16 8 ([[], [], [2, 3], [3]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [3] [] ∧ LexLE [] [])) h)

private theorem k16t8_cover511 : ∀ P ∈ pathPatterns 3 3 [2, 3], HasCheckedCertificate 16 8 ([[], [], [2, 3]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [2, 3] [] ∧ LexLE [] [])) h)
      · intro q
        fin_cases q
        · exact by
            constructor
            · exact by
                intro h
                exact False.elim ((by decide : ¬ (LexLE [2, 3] [1] ∧ LexLE [1] [1])) h)
            · intro q
              fin_cases q
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [2, 3] [1, 1] ∧ LexLE [1, 1] [1, 1])) h)
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [2, 3] [1, 2] ∧ LexLE [1, 2] [2, 1])) h)
        · exact by
            constructor
            · exact by
                intro h
                exact False.elim ((by decide : ¬ (LexLE [2, 3] [2] ∧ LexLE [2] [2])) h)
            · intro q
              fin_cases q
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [2, 3] [2, 1] ∧ LexLE [2, 1] [1, 2])) h)
        · exact by
            constructor
            · exact by
                intro _
                exact k16t8_cover512
            · intro q
              exact Fin.elim0 q

private theorem k16t8_cover513 : ∀ P ∈ pathPatterns 2 1 [2, 3, 2], HasCheckedCertificate 16 8 ([[], [], [2, 3, 2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [2, 3, 2] [] ∧ LexLE [] [])) h)
      · intro q
        fin_cases q
        · exact by
            intro h
            exact False.elim ((by decide : ¬ (LexLE [2, 3, 2] [1] ∧ LexLE [1] [1])) h)

private theorem k16t8_cover514 : ∀ P ∈ pathPatterns 2 0 [2, 3, 3], HasCheckedCertificate 16 8 ([[], [], [2, 3, 3]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [2, 3, 3] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k16t8_cover515 : ∀ P ∈ pathPatterns 3 2 [2, 4], HasCheckedCertificate 16 8 ([[], [], [2, 4]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [2, 4] [] ∧ LexLE [] [])) h)
      · intro q
        fin_cases q
        · exact by
            constructor
            · exact by
                intro h
                exact False.elim ((by decide : ¬ (LexLE [2, 4] [1] ∧ LexLE [1] [1])) h)
            · intro q
              fin_cases q
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [2, 4] [1, 1] ∧ LexLE [1, 1] [1, 1])) h)
        · exact by
            constructor
            · exact by
                intro h
                exact False.elim ((by decide : ¬ (LexLE [2, 4] [2] ∧ LexLE [2] [2])) h)
            · intro q
              exact Fin.elim0 q

private theorem k16t8_cover516 : ∀ P ∈ pathPatterns 2 0 [2, 4, 2], HasCheckedCertificate 16 8 ([[], [], [2, 4, 2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [2, 4, 2] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k16t8_cover517 : ∀ P ∈ pathPatterns 3 1 [2, 5], HasCheckedCertificate 16 8 ([[], [], [2, 5]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [2, 5] [] ∧ LexLE [] [])) h)
      · intro q
        fin_cases q
        · exact by
            constructor
            · exact by
                intro h
                exact False.elim ((by decide : ¬ (LexLE [2, 5] [1] ∧ LexLE [1] [1])) h)
            · intro q
              exact Fin.elim0 q

private theorem k16t8_cover518 : ∀ P ∈ pathPatterns 3 0 [2, 6], HasCheckedCertificate 16 8 ([[], [], [2, 6]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [2, 6] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k16t8_seq467 : amountSequenceForall 4 6 (fun tail =>
    (LexLE [] ([2] ++ tail) ∧ LexLE ([2] ++ tail) ([2] ++ tail).reverse) →
    ∀ P ∈ pathPatterns (5 - ([2] ++ tail).length) (8 - ([2] ++ tail).sum) ([2] ++ tail),
      HasCheckedCertificate 16 8 ([[], []] ++ (([2] ++ tail) :: P))) :=
by
  constructor
  · exact by
      intro _
      exact k16t8_cover468
  · intro q
    fin_cases q
    · exact k16t8_seq486

    · exact by
        constructor
        · exact by
            intro _
            exact k16t8_cover502
        · intro q
          fin_cases q
          · exact by
              constructor
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [] [2, 2, 1] ∧ LexLE [2, 2, 1] [1, 2, 2])) h)
              · intro q
                fin_cases q
                · exact by
                    constructor
                    · exact by
                        intro h
                        exact False.elim ((by decide : ¬ (LexLE [] [2, 2, 1, 1] ∧ LexLE [2, 2, 1, 1] [1, 1, 2, 2])) h)
                    · intro q
                      fin_cases q
                      · exact by
                          intro h
                          exact False.elim ((by decide : ¬ (LexLE [] [2, 2, 1, 1, 1] ∧ LexLE [2, 2, 1, 1, 1] [1, 1, 1, 2, 2])) h)
                      · exact by
                          intro h
                          exact False.elim ((by decide : ¬ (LexLE [] [2, 2, 1, 1, 2] ∧ LexLE [2, 2, 1, 1, 2] [2, 1, 1, 2, 2])) h)
                · exact by
                    constructor
                    · exact by
                        intro h
                        exact False.elim ((by decide : ¬ (LexLE [] [2, 2, 1, 2] ∧ LexLE [2, 2, 1, 2] [2, 1, 2, 2])) h)
                    · intro q
                      fin_cases q
                      · exact by
                          intro h
                          exact False.elim ((by decide : ¬ (LexLE [] [2, 2, 1, 2, 1] ∧ LexLE [2, 2, 1, 2, 1] [1, 2, 1, 2, 2])) h)
                · exact by
                    constructor
                    · exact by
                        intro _
                        exact k16t8_cover506
                    · intro q
                      exact Fin.elim0 q
          · exact by
              constructor
              · exact by
                  intro _
                  exact k16t8_cover507
              · intro q
                fin_cases q
                · exact by
                    constructor
                    · exact by
                        intro h
                        exact False.elim ((by decide : ¬ (LexLE [] [2, 2, 2, 1] ∧ LexLE [2, 2, 2, 1] [1, 2, 2, 2])) h)
                    · intro q
                      fin_cases q
                      · exact by
                          intro h
                          exact False.elim ((by decide : ¬ (LexLE [] [2, 2, 2, 1, 1] ∧ LexLE [2, 2, 2, 1, 1] [1, 1, 2, 2, 2])) h)
                · exact by
                    constructor
                    · exact by
                        intro _
                        exact k16t8_cover508
                    · intro q
                      exact Fin.elim0 q
          · exact by
              constructor
              · exact by
                  intro _
                  exact k16t8_cover509
              · intro q
                fin_cases q
                · exact by
                    constructor
                    · exact by
                        intro h
                        exact False.elim ((by decide : ¬ (LexLE [] [2, 2, 3, 1] ∧ LexLE [2, 2, 3, 1] [1, 3, 2, 2])) h)
                    · intro q
                      exact Fin.elim0 q
          · exact by
              constructor
              · exact by
                  intro _
                  exact k16t8_cover510
              · intro q
                exact Fin.elim0 q
    · exact by
        constructor
        · exact by
            intro _
            exact k16t8_cover511
        · intro q
          fin_cases q
          · exact by
              constructor
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [] [2, 3, 1] ∧ LexLE [2, 3, 1] [1, 3, 2])) h)
              · intro q
                fin_cases q
                · exact by
                    constructor
                    · exact by
                        intro h
                        exact False.elim ((by decide : ¬ (LexLE [] [2, 3, 1, 1] ∧ LexLE [2, 3, 1, 1] [1, 1, 3, 2])) h)
                    · intro q
                      fin_cases q
                      · exact by
                          intro h
                          exact False.elim ((by decide : ¬ (LexLE [] [2, 3, 1, 1, 1] ∧ LexLE [2, 3, 1, 1, 1] [1, 1, 1, 3, 2])) h)
                · exact by
                    constructor
                    · exact by
                        intro h
                        exact False.elim ((by decide : ¬ (LexLE [] [2, 3, 1, 2] ∧ LexLE [2, 3, 1, 2] [2, 1, 3, 2])) h)
                    · intro q
                      exact Fin.elim0 q
          · exact by
              constructor
              · exact by
                  intro _
                  exact k16t8_cover513
              · intro q
                fin_cases q
                · exact by
                    constructor
                    · exact by
                        intro h
                        exact False.elim ((by decide : ¬ (LexLE [] [2, 3, 2, 1] ∧ LexLE [2, 3, 2, 1] [1, 2, 3, 2])) h)
                    · intro q
                      exact Fin.elim0 q
          · exact by
              constructor
              · exact by
                  intro _
                  exact k16t8_cover514
              · intro q
                exact Fin.elim0 q
    · exact by
        constructor
        · exact by
            intro _
            exact k16t8_cover515
        · intro q
          fin_cases q
          · exact by
              constructor
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [] [2, 4, 1] ∧ LexLE [2, 4, 1] [1, 4, 2])) h)
              · intro q
                fin_cases q
                · exact by
                    constructor
                    · exact by
                        intro h
                        exact False.elim ((by decide : ¬ (LexLE [] [2, 4, 1, 1] ∧ LexLE [2, 4, 1, 1] [1, 1, 4, 2])) h)
                    · intro q
                      exact Fin.elim0 q
          · exact by
              constructor
              · exact by
                  intro _
                  exact k16t8_cover516
              · intro q
                exact Fin.elim0 q
    · exact by
        constructor
        · exact by
            intro _
            exact k16t8_cover517
        · intro q
          fin_cases q
          · exact by
              constructor
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [] [2, 5, 1] ∧ LexLE [2, 5, 1] [1, 5, 2])) h)
              · intro q
                exact Fin.elim0 q
    · exact by
        constructor
        · exact by
            intro _
            exact k16t8_cover518
        · intro q
          exact Fin.elim0 q

private theorem k16t8_cover522 : ∀ P ∈ pathPatterns 2 2 [3], HasCheckedCertificate 16 8 ([[], [], [3], [3]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [3] [] ∧ LexLE [] [])) h)
      · intro q
        fin_cases q
        · exact by
            intro h
            exact False.elim ((by decide : ¬ (LexLE [3] [1] ∧ LexLE [1] [1])) h)
        · exact by
            intro h
            exact False.elim ((by decide : ¬ (LexLE [3] [2] ∧ LexLE [2] [2])) h)

private theorem k16t8_cover523 : ∀ P ∈ pathPatterns 2 1 [4], HasCheckedCertificate 16 8 ([[], [], [3], [4]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [4] [] ∧ LexLE [] [])) h)
      · intro q
        fin_cases q
        · exact by
            intro h
            exact False.elim ((by decide : ¬ (LexLE [4] [1] ∧ LexLE [1] [1])) h)

private theorem k16t8_cover524 : ∀ P ∈ pathPatterns 2 0 [5], HasCheckedCertificate 16 8 ([[], [], [3], [5]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [5] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k16t8_seq521 : amountSequenceForall 3 5 (fun tail =>
    (LexLE [3] ([] ++ tail) ∧ LexLE ([] ++ tail) ([] ++ tail).reverse) →
    ∀ P ∈ pathPatterns (3 - ([] ++ tail).length) (5 - ([] ++ tail).sum) ([] ++ tail),
      HasCheckedCertificate 16 8 ([[], [], [3]] ++ (([] ++ tail) :: P))) :=
by
  constructor
  · exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [3] [] ∧ LexLE [] [])) h)
  · intro q
    fin_cases q
    · exact by
        constructor
        · exact by
            intro h
            exact False.elim ((by decide : ¬ (LexLE [3] [1] ∧ LexLE [1] [1])) h)
        · intro q
          fin_cases q
          · exact by
              constructor
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [3] [1, 1] ∧ LexLE [1, 1] [1, 1])) h)
              · intro q
                fin_cases q
                · exact by
                    intro h
                    exact False.elim ((by decide : ¬ (LexLE [3] [1, 1, 1] ∧ LexLE [1, 1, 1] [1, 1, 1])) h)
                · exact by
                    intro h
                    exact False.elim ((by decide : ¬ (LexLE [3] [1, 1, 2] ∧ LexLE [1, 1, 2] [2, 1, 1])) h)
                · exact by
                    intro h
                    exact False.elim ((by decide : ¬ (LexLE [3] [1, 1, 3] ∧ LexLE [1, 1, 3] [3, 1, 1])) h)
          · exact by
              constructor
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [3] [1, 2] ∧ LexLE [1, 2] [2, 1])) h)
              · intro q
                fin_cases q
                · exact by
                    intro h
                    exact False.elim ((by decide : ¬ (LexLE [3] [1, 2, 1] ∧ LexLE [1, 2, 1] [1, 2, 1])) h)
                · exact by
                    intro h
                    exact False.elim ((by decide : ¬ (LexLE [3] [1, 2, 2] ∧ LexLE [1, 2, 2] [2, 2, 1])) h)
          · exact by
              constructor
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [3] [1, 3] ∧ LexLE [1, 3] [3, 1])) h)
              · intro q
                fin_cases q
                · exact by
                    intro h
                    exact False.elim ((by decide : ¬ (LexLE [3] [1, 3, 1] ∧ LexLE [1, 3, 1] [1, 3, 1])) h)
          · exact by
              constructor
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [3] [1, 4] ∧ LexLE [1, 4] [4, 1])) h)
              · intro q
                exact Fin.elim0 q
    · exact by
        constructor
        · exact by
            intro h
            exact False.elim ((by decide : ¬ (LexLE [3] [2] ∧ LexLE [2] [2])) h)
        · intro q
          fin_cases q
          · exact by
              constructor
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [3] [2, 1] ∧ LexLE [2, 1] [1, 2])) h)
              · intro q
                fin_cases q
                · exact by
                    intro h
                    exact False.elim ((by decide : ¬ (LexLE [3] [2, 1, 1] ∧ LexLE [2, 1, 1] [1, 1, 2])) h)
                · exact by
                    intro h
                    exact False.elim ((by decide : ¬ (LexLE [3] [2, 1, 2] ∧ LexLE [2, 1, 2] [2, 1, 2])) h)
          · exact by
              constructor
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [3] [2, 2] ∧ LexLE [2, 2] [2, 2])) h)
              · intro q
                fin_cases q
                · exact by
                    intro h
                    exact False.elim ((by decide : ¬ (LexLE [3] [2, 2, 1] ∧ LexLE [2, 2, 1] [1, 2, 2])) h)
          · exact by
              constructor
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [3] [2, 3] ∧ LexLE [2, 3] [3, 2])) h)
              · intro q
                exact Fin.elim0 q
    · exact by
        constructor
        · exact by
            intro _
            exact k16t8_cover522
        · intro q
          fin_cases q
          · exact by
              constructor
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [3] [3, 1] ∧ LexLE [3, 1] [1, 3])) h)
              · intro q
                fin_cases q
                · exact by
                    intro h
                    exact False.elim ((by decide : ¬ (LexLE [3] [3, 1, 1] ∧ LexLE [3, 1, 1] [1, 1, 3])) h)
          · exact by
              constructor
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [3] [3, 2] ∧ LexLE [3, 2] [2, 3])) h)
              · intro q
                exact Fin.elim0 q
    · exact by
        constructor
        · exact by
            intro _
            exact k16t8_cover523
        · intro q
          fin_cases q
          · exact by
              constructor
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [3] [4, 1] ∧ LexLE [4, 1] [1, 4])) h)
              · intro q
                exact Fin.elim0 q
    · exact by
        constructor
        · exact by
            intro _
            exact k16t8_cover524
        · intro q
          exact Fin.elim0 q

private theorem k16t8_cover520 : ∀ P ∈ pathPatterns 4 5 [3], HasCheckedCertificate 16 8 ([[], [], [3]] ++ P) := by
  apply pathPatterns_forall_step
  exact k16t8_seq521


private theorem k16t8_cover525 : ∀ P ∈ pathPatterns 1 0 [3, 1, 1, 3], HasCheckedCertificate 16 8 ([[], [], [3, 1, 1, 3]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [3, 1, 1, 3] [] ∧ LexLE [] [])) h)

private theorem k16t8_cover526 : ∀ P ∈ pathPatterns 2 1 [3, 1, 3], HasCheckedCertificate 16 8 ([[], [], [3, 1, 3]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [3, 1, 3] [] ∧ LexLE [] [])) h)
      · intro q
        fin_cases q
        · exact by
            intro h
            exact False.elim ((by decide : ¬ (LexLE [3, 1, 3] [1] ∧ LexLE [1] [1])) h)

private theorem k16t8_cover527 : ∀ P ∈ pathPatterns 2 0 [3, 1, 4], HasCheckedCertificate 16 8 ([[], [], [3, 1, 4]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [3, 1, 4] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k16t8_cover528 : ∀ P ∈ pathPatterns 2 0 [3, 2, 3], HasCheckedCertificate 16 8 ([[], [], [3, 2, 3]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [3, 2, 3] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k16t8_cover529 : ∀ P ∈ pathPatterns 3 2 [3, 3], HasCheckedCertificate 16 8 ([[], [], [3, 3]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [3, 3] [] ∧ LexLE [] [])) h)
      · intro q
        fin_cases q
        · exact by
            constructor
            · exact by
                intro h
                exact False.elim ((by decide : ¬ (LexLE [3, 3] [1] ∧ LexLE [1] [1])) h)
            · intro q
              fin_cases q
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [3, 3] [1, 1] ∧ LexLE [1, 1] [1, 1])) h)
        · exact by
            constructor
            · exact by
                intro h
                exact False.elim ((by decide : ¬ (LexLE [3, 3] [2] ∧ LexLE [2] [2])) h)
            · intro q
              exact Fin.elim0 q

private theorem k16t8_cover530 : ∀ P ∈ pathPatterns 3 1 [3, 4], HasCheckedCertificate 16 8 ([[], [], [3, 4]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [3, 4] [] ∧ LexLE [] [])) h)
      · intro q
        fin_cases q
        · exact by
            constructor
            · exact by
                intro h
                exact False.elim ((by decide : ¬ (LexLE [3, 4] [1] ∧ LexLE [1] [1])) h)
            · intro q
              exact Fin.elim0 q

private theorem k16t8_cover531 : ∀ P ∈ pathPatterns 3 0 [3, 5], HasCheckedCertificate 16 8 ([[], [], [3, 5]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [3, 5] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k16t8_seq519 : amountSequenceForall 4 5 (fun tail =>
    (LexLE [] ([3] ++ tail) ∧ LexLE ([3] ++ tail) ([3] ++ tail).reverse) →
    ∀ P ∈ pathPatterns (5 - ([3] ++ tail).length) (8 - ([3] ++ tail).sum) ([3] ++ tail),
      HasCheckedCertificate 16 8 ([[], []] ++ (([3] ++ tail) :: P))) :=
by
  constructor
  · exact by
      intro _
      exact k16t8_cover520
  · intro q
    fin_cases q
    · exact by
        constructor
        · exact by
            intro h
            exact False.elim ((by decide : ¬ (LexLE [] [3, 1] ∧ LexLE [3, 1] [1, 3])) h)
        · intro q
          fin_cases q
          · exact by
              constructor
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [] [3, 1, 1] ∧ LexLE [3, 1, 1] [1, 1, 3])) h)
              · intro q
                fin_cases q
                · exact by
                    constructor
                    · exact by
                        intro h
                        exact False.elim ((by decide : ¬ (LexLE [] [3, 1, 1, 1] ∧ LexLE [3, 1, 1, 1] [1, 1, 1, 3])) h)
                    · intro q
                      fin_cases q
                      · exact by
                          intro h
                          exact False.elim ((by decide : ¬ (LexLE [] [3, 1, 1, 1, 1] ∧ LexLE [3, 1, 1, 1, 1] [1, 1, 1, 1, 3])) h)
                      · exact by
                          intro h
                          exact False.elim ((by decide : ¬ (LexLE [] [3, 1, 1, 1, 2] ∧ LexLE [3, 1, 1, 1, 2] [2, 1, 1, 1, 3])) h)
                · exact by
                    constructor
                    · exact by
                        intro h
                        exact False.elim ((by decide : ¬ (LexLE [] [3, 1, 1, 2] ∧ LexLE [3, 1, 1, 2] [2, 1, 1, 3])) h)
                    · intro q
                      fin_cases q
                      · exact by
                          intro h
                          exact False.elim ((by decide : ¬ (LexLE [] [3, 1, 1, 2, 1] ∧ LexLE [3, 1, 1, 2, 1] [1, 2, 1, 1, 3])) h)
                · exact by
                    constructor
                    · exact by
                        intro _
                        exact k16t8_cover525
                    · intro q
                      exact Fin.elim0 q
          · exact by
              constructor
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [] [3, 1, 2] ∧ LexLE [3, 1, 2] [2, 1, 3])) h)
              · intro q
                fin_cases q
                · exact by
                    constructor
                    · exact by
                        intro h
                        exact False.elim ((by decide : ¬ (LexLE [] [3, 1, 2, 1] ∧ LexLE [3, 1, 2, 1] [1, 2, 1, 3])) h)
                    · intro q
                      fin_cases q
                      · exact by
                          intro h
                          exact False.elim ((by decide : ¬ (LexLE [] [3, 1, 2, 1, 1] ∧ LexLE [3, 1, 2, 1, 1] [1, 1, 2, 1, 3])) h)
                · exact by
                    constructor
                    · exact by
                        intro h
                        exact False.elim ((by decide : ¬ (LexLE [] [3, 1, 2, 2] ∧ LexLE [3, 1, 2, 2] [2, 2, 1, 3])) h)
                    · intro q
                      exact Fin.elim0 q
          · exact by
              constructor
              · exact by
                  intro _
                  exact k16t8_cover526
              · intro q
                fin_cases q
                · exact by
                    constructor
                    · exact by
                        intro h
                        exact False.elim ((by decide : ¬ (LexLE [] [3, 1, 3, 1] ∧ LexLE [3, 1, 3, 1] [1, 3, 1, 3])) h)
                    · intro q
                      exact Fin.elim0 q
          · exact by
              constructor
              · exact by
                  intro _
                  exact k16t8_cover527
              · intro q
                exact Fin.elim0 q
    · exact by
        constructor
        · exact by
            intro h
            exact False.elim ((by decide : ¬ (LexLE [] [3, 2] ∧ LexLE [3, 2] [2, 3])) h)
        · intro q
          fin_cases q
          · exact by
              constructor
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [] [3, 2, 1] ∧ LexLE [3, 2, 1] [1, 2, 3])) h)
              · intro q
                fin_cases q
                · exact by
                    constructor
                    · exact by
                        intro h
                        exact False.elim ((by decide : ¬ (LexLE [] [3, 2, 1, 1] ∧ LexLE [3, 2, 1, 1] [1, 1, 2, 3])) h)
                    · intro q
                      fin_cases q
                      · exact by
                          intro h
                          exact False.elim ((by decide : ¬ (LexLE [] [3, 2, 1, 1, 1] ∧ LexLE [3, 2, 1, 1, 1] [1, 1, 1, 2, 3])) h)
                · exact by
                    constructor
                    · exact by
                        intro h
                        exact False.elim ((by decide : ¬ (LexLE [] [3, 2, 1, 2] ∧ LexLE [3, 2, 1, 2] [2, 1, 2, 3])) h)
                    · intro q
                      exact Fin.elim0 q
          · exact by
              constructor
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [] [3, 2, 2] ∧ LexLE [3, 2, 2] [2, 2, 3])) h)
              · intro q
                fin_cases q
                · exact by
                    constructor
                    · exact by
                        intro h
                        exact False.elim ((by decide : ¬ (LexLE [] [3, 2, 2, 1] ∧ LexLE [3, 2, 2, 1] [1, 2, 2, 3])) h)
                    · intro q
                      exact Fin.elim0 q
          · exact by
              constructor
              · exact by
                  intro _
                  exact k16t8_cover528
              · intro q
                exact Fin.elim0 q
    · exact by
        constructor
        · exact by
            intro _
            exact k16t8_cover529
        · intro q
          fin_cases q
          · exact by
              constructor
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [] [3, 3, 1] ∧ LexLE [3, 3, 1] [1, 3, 3])) h)
              · intro q
                fin_cases q
                · exact by
                    constructor
                    · exact by
                        intro h
                        exact False.elim ((by decide : ¬ (LexLE [] [3, 3, 1, 1] ∧ LexLE [3, 3, 1, 1] [1, 1, 3, 3])) h)
                    · intro q
                      exact Fin.elim0 q
          · exact by
              constructor
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [] [3, 3, 2] ∧ LexLE [3, 3, 2] [2, 3, 3])) h)
              · intro q
                exact Fin.elim0 q
    · exact by
        constructor
        · exact by
            intro _
            exact k16t8_cover530
        · intro q
          fin_cases q
          · exact by
              constructor
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [] [3, 4, 1] ∧ LexLE [3, 4, 1] [1, 4, 3])) h)
              · intro q
                exact Fin.elim0 q
    · exact by
        constructor
        · exact by
            intro _
            exact k16t8_cover531
        · intro q
          exact Fin.elim0 q

private theorem k16t8_cover533 : ∀ P ∈ pathPatterns 2 0 [4], HasCheckedCertificate 16 8 ([[], [], [4], [4]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [4] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k16t8_cover532 : ∀ P ∈ pathPatterns 4 4 [4], HasCheckedCertificate 16 8 ([[], [], [4]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [4] [] ∧ LexLE [] [])) h)
      · intro q
        fin_cases q
        · exact by
            constructor
            · exact by
                intro h
                exact False.elim ((by decide : ¬ (LexLE [4] [1] ∧ LexLE [1] [1])) h)
            · intro q
              fin_cases q
              · exact by
                  constructor
                  · exact by
                      intro h
                      exact False.elim ((by decide : ¬ (LexLE [4] [1, 1] ∧ LexLE [1, 1] [1, 1])) h)
                  · intro q
                    fin_cases q
                    · exact by
                        intro h
                        exact False.elim ((by decide : ¬ (LexLE [4] [1, 1, 1] ∧ LexLE [1, 1, 1] [1, 1, 1])) h)
                    · exact by
                        intro h
                        exact False.elim ((by decide : ¬ (LexLE [4] [1, 1, 2] ∧ LexLE [1, 1, 2] [2, 1, 1])) h)
              · exact by
                  constructor
                  · exact by
                      intro h
                      exact False.elim ((by decide : ¬ (LexLE [4] [1, 2] ∧ LexLE [1, 2] [2, 1])) h)
                  · intro q
                    fin_cases q
                    · exact by
                        intro h
                        exact False.elim ((by decide : ¬ (LexLE [4] [1, 2, 1] ∧ LexLE [1, 2, 1] [1, 2, 1])) h)
              · exact by
                  constructor
                  · exact by
                      intro h
                      exact False.elim ((by decide : ¬ (LexLE [4] [1, 3] ∧ LexLE [1, 3] [3, 1])) h)
                  · intro q
                    exact Fin.elim0 q
        · exact by
            constructor
            · exact by
                intro h
                exact False.elim ((by decide : ¬ (LexLE [4] [2] ∧ LexLE [2] [2])) h)
            · intro q
              fin_cases q
              · exact by
                  constructor
                  · exact by
                      intro h
                      exact False.elim ((by decide : ¬ (LexLE [4] [2, 1] ∧ LexLE [2, 1] [1, 2])) h)
                  · intro q
                    fin_cases q
                    · exact by
                        intro h
                        exact False.elim ((by decide : ¬ (LexLE [4] [2, 1, 1] ∧ LexLE [2, 1, 1] [1, 1, 2])) h)
              · exact by
                  constructor
                  · exact by
                      intro h
                      exact False.elim ((by decide : ¬ (LexLE [4] [2, 2] ∧ LexLE [2, 2] [2, 2])) h)
                  · intro q
                    exact Fin.elim0 q
        · exact by
            constructor
            · exact by
                intro h
                exact False.elim ((by decide : ¬ (LexLE [4] [3] ∧ LexLE [3] [3])) h)
            · intro q
              fin_cases q
              · exact by
                  constructor
                  · exact by
                      intro h
                      exact False.elim ((by decide : ¬ (LexLE [4] [3, 1] ∧ LexLE [3, 1] [1, 3])) h)
                  · intro q
                    exact Fin.elim0 q
        · exact by
            constructor
            · exact by
                intro _
                exact k16t8_cover533
            · intro q
              exact Fin.elim0 q

private theorem k16t8_cover534 : ∀ P ∈ pathPatterns 3 0 [4, 4], HasCheckedCertificate 16 8 ([[], [], [4, 4]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [4, 4] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k16t8_cover535 : ∀ P ∈ pathPatterns 4 3 [5], HasCheckedCertificate 16 8 ([[], [], [5]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [5] [] ∧ LexLE [] [])) h)
      · intro q
        fin_cases q
        · exact by
            constructor
            · exact by
                intro h
                exact False.elim ((by decide : ¬ (LexLE [5] [1] ∧ LexLE [1] [1])) h)
            · intro q
              fin_cases q
              · exact by
                  constructor
                  · exact by
                      intro h
                      exact False.elim ((by decide : ¬ (LexLE [5] [1, 1] ∧ LexLE [1, 1] [1, 1])) h)
                  · intro q
                    fin_cases q
                    · exact by
                        intro h
                        exact False.elim ((by decide : ¬ (LexLE [5] [1, 1, 1] ∧ LexLE [1, 1, 1] [1, 1, 1])) h)
              · exact by
                  constructor
                  · exact by
                      intro h
                      exact False.elim ((by decide : ¬ (LexLE [5] [1, 2] ∧ LexLE [1, 2] [2, 1])) h)
                  · intro q
                    exact Fin.elim0 q
        · exact by
            constructor
            · exact by
                intro h
                exact False.elim ((by decide : ¬ (LexLE [5] [2] ∧ LexLE [2] [2])) h)
            · intro q
              fin_cases q
              · exact by
                  constructor
                  · exact by
                      intro h
                      exact False.elim ((by decide : ¬ (LexLE [5] [2, 1] ∧ LexLE [2, 1] [1, 2])) h)
                  · intro q
                    exact Fin.elim0 q
        · exact by
            constructor
            · exact by
                intro h
                exact False.elim ((by decide : ¬ (LexLE [5] [3] ∧ LexLE [3] [3])) h)
            · intro q
              exact Fin.elim0 q

private theorem k16t8_cover536 : ∀ P ∈ pathPatterns 4 2 [6], HasCheckedCertificate 16 8 ([[], [], [6]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [6] [] ∧ LexLE [] [])) h)
      · intro q
        fin_cases q
        · exact by
            constructor
            · exact by
                intro h
                exact False.elim ((by decide : ¬ (LexLE [6] [1] ∧ LexLE [1] [1])) h)
            · intro q
              fin_cases q
              · exact by
                  constructor
                  · exact by
                      intro h
                      exact False.elim ((by decide : ¬ (LexLE [6] [1, 1] ∧ LexLE [1, 1] [1, 1])) h)
                  · intro q
                    exact Fin.elim0 q
        · exact by
            constructor
            · exact by
                intro h
                exact False.elim ((by decide : ¬ (LexLE [6] [2] ∧ LexLE [2] [2])) h)
            · intro q
              exact Fin.elim0 q

private theorem k16t8_cover537 : ∀ P ∈ pathPatterns 4 1 [7], HasCheckedCertificate 16 8 ([[], [], [7]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [7] [] ∧ LexLE [] [])) h)
      · intro q
        fin_cases q
        · exact by
            constructor
            · exact by
                intro h
                exact False.elim ((by decide : ¬ (LexLE [7] [1] ∧ LexLE [1] [1])) h)
            · intro q
              exact Fin.elim0 q

private theorem k16t8_cover538 : ∀ P ∈ pathPatterns 4 0 [8], HasCheckedCertificate 16 8 ([[], [], [8]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [8] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k16t8_seq6 : amountSequenceForall 5 8 (fun tail =>
    (LexLE [] ([] ++ tail) ∧ LexLE ([] ++ tail) ([] ++ tail).reverse) →
    ∀ P ∈ pathPatterns (5 - ([] ++ tail).length) (8 - ([] ++ tail).sum) ([] ++ tail),
      HasCheckedCertificate 16 8 ([[], []] ++ (([] ++ tail) :: P))) :=
by
  constructor
  · exact by
      intro _
      exact k16t8_cover7
  · intro q
    fin_cases q
    · exact k16t8_seq273

    · exact k16t8_seq467

    · exact k16t8_seq519

    · exact by
        constructor
        · exact by
            intro _
            exact k16t8_cover532
        · intro q
          fin_cases q
          · exact by
              constructor
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [] [4, 1] ∧ LexLE [4, 1] [1, 4])) h)
              · intro q
                fin_cases q
                · exact by
                    constructor
                    · exact by
                        intro h
                        exact False.elim ((by decide : ¬ (LexLE [] [4, 1, 1] ∧ LexLE [4, 1, 1] [1, 1, 4])) h)
                    · intro q
                      fin_cases q
                      · exact by
                          constructor
                          · exact by
                              intro h
                              exact False.elim ((by decide : ¬ (LexLE [] [4, 1, 1, 1] ∧ LexLE [4, 1, 1, 1] [1, 1, 1, 4])) h)
                          · intro q
                            fin_cases q
                            · exact by
                                intro h
                                exact False.elim ((by decide : ¬ (LexLE [] [4, 1, 1, 1, 1] ∧ LexLE [4, 1, 1, 1, 1] [1, 1, 1, 1, 4])) h)
                      · exact by
                          constructor
                          · exact by
                              intro h
                              exact False.elim ((by decide : ¬ (LexLE [] [4, 1, 1, 2] ∧ LexLE [4, 1, 1, 2] [2, 1, 1, 4])) h)
                          · intro q
                            exact Fin.elim0 q
                · exact by
                    constructor
                    · exact by
                        intro h
                        exact False.elim ((by decide : ¬ (LexLE [] [4, 1, 2] ∧ LexLE [4, 1, 2] [2, 1, 4])) h)
                    · intro q
                      fin_cases q
                      · exact by
                          constructor
                          · exact by
                              intro h
                              exact False.elim ((by decide : ¬ (LexLE [] [4, 1, 2, 1] ∧ LexLE [4, 1, 2, 1] [1, 2, 1, 4])) h)
                          · intro q
                            exact Fin.elim0 q
                · exact by
                    constructor
                    · exact by
                        intro h
                        exact False.elim ((by decide : ¬ (LexLE [] [4, 1, 3] ∧ LexLE [4, 1, 3] [3, 1, 4])) h)
                    · intro q
                      exact Fin.elim0 q
          · exact by
              constructor
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [] [4, 2] ∧ LexLE [4, 2] [2, 4])) h)
              · intro q
                fin_cases q
                · exact by
                    constructor
                    · exact by
                        intro h
                        exact False.elim ((by decide : ¬ (LexLE [] [4, 2, 1] ∧ LexLE [4, 2, 1] [1, 2, 4])) h)
                    · intro q
                      fin_cases q
                      · exact by
                          constructor
                          · exact by
                              intro h
                              exact False.elim ((by decide : ¬ (LexLE [] [4, 2, 1, 1] ∧ LexLE [4, 2, 1, 1] [1, 1, 2, 4])) h)
                          · intro q
                            exact Fin.elim0 q
                · exact by
                    constructor
                    · exact by
                        intro h
                        exact False.elim ((by decide : ¬ (LexLE [] [4, 2, 2] ∧ LexLE [4, 2, 2] [2, 2, 4])) h)
                    · intro q
                      exact Fin.elim0 q
          · exact by
              constructor
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [] [4, 3] ∧ LexLE [4, 3] [3, 4])) h)
              · intro q
                fin_cases q
                · exact by
                    constructor
                    · exact by
                        intro h
                        exact False.elim ((by decide : ¬ (LexLE [] [4, 3, 1] ∧ LexLE [4, 3, 1] [1, 3, 4])) h)
                    · intro q
                      exact Fin.elim0 q
          · exact by
              constructor
              · exact by
                  intro _
                  exact k16t8_cover534
              · intro q
                exact Fin.elim0 q
    · exact by
        constructor
        · exact by
            intro _
            exact k16t8_cover535
        · intro q
          fin_cases q
          · exact by
              constructor
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [] [5, 1] ∧ LexLE [5, 1] [1, 5])) h)
              · intro q
                fin_cases q
                · exact by
                    constructor
                    · exact by
                        intro h
                        exact False.elim ((by decide : ¬ (LexLE [] [5, 1, 1] ∧ LexLE [5, 1, 1] [1, 1, 5])) h)
                    · intro q
                      fin_cases q
                      · exact by
                          constructor
                          · exact by
                              intro h
                              exact False.elim ((by decide : ¬ (LexLE [] [5, 1, 1, 1] ∧ LexLE [5, 1, 1, 1] [1, 1, 1, 5])) h)
                          · intro q
                            exact Fin.elim0 q
                · exact by
                    constructor
                    · exact by
                        intro h
                        exact False.elim ((by decide : ¬ (LexLE [] [5, 1, 2] ∧ LexLE [5, 1, 2] [2, 1, 5])) h)
                    · intro q
                      exact Fin.elim0 q
          · exact by
              constructor
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [] [5, 2] ∧ LexLE [5, 2] [2, 5])) h)
              · intro q
                fin_cases q
                · exact by
                    constructor
                    · exact by
                        intro h
                        exact False.elim ((by decide : ¬ (LexLE [] [5, 2, 1] ∧ LexLE [5, 2, 1] [1, 2, 5])) h)
                    · intro q
                      exact Fin.elim0 q
          · exact by
              constructor
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [] [5, 3] ∧ LexLE [5, 3] [3, 5])) h)
              · intro q
                exact Fin.elim0 q
    · exact by
        constructor
        · exact by
            intro _
            exact k16t8_cover536
        · intro q
          fin_cases q
          · exact by
              constructor
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [] [6, 1] ∧ LexLE [6, 1] [1, 6])) h)
              · intro q
                fin_cases q
                · exact by
                    constructor
                    · exact by
                        intro h
                        exact False.elim ((by decide : ¬ (LexLE [] [6, 1, 1] ∧ LexLE [6, 1, 1] [1, 1, 6])) h)
                    · intro q
                      exact Fin.elim0 q
          · exact by
              constructor
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [] [6, 2] ∧ LexLE [6, 2] [2, 6])) h)
              · intro q
                exact Fin.elim0 q
    · exact by
        constructor
        · exact by
            intro _
            exact k16t8_cover537
        · intro q
          fin_cases q
          · exact by
              constructor
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [] [7, 1] ∧ LexLE [7, 1] [1, 7])) h)
              · intro q
                exact Fin.elim0 q
    · exact by
        constructor
        · exact by
            intro _
            exact k16t8_cover538
        · intro q
          exact Fin.elim0 q

private theorem k16t8_cover5 : ∀ P ∈ pathPatterns 6 8 [], HasCheckedCertificate 16 8 ([[], []] ++ P) := by
  apply pathPatterns_forall_step
  exact k16t8_seq6


private theorem k16t8_cover544 : ∀ P ∈ pathPatterns 1 5 [1], HasCheckedCertificate 16 8 ([[], [1], [1], [1]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [1] [] ∧ LexLE [] [])) h)

private theorem k16t8_cover545 : ∀ P ∈ pathPatterns 0 4 [1, 1], HasCheckedCertificate 16 8 ([[], [1], [1], [1, 1]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k16t8p258, Certificates.k16t8p258_check⟩

private theorem k16t8_cover546 : ∀ P ∈ pathPatterns 0 3 [1, 2], HasCheckedCertificate 16 8 ([[], [1], [1], [1, 2]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k16t8p259, Certificates.k16t8p259_check⟩

private theorem k16t8_cover547 : ∀ P ∈ pathPatterns 0 2 [1, 3], HasCheckedCertificate 16 8 ([[], [1], [1], [1, 3]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k16t8p260, Certificates.k16t8p260_check⟩

private theorem k16t8_cover548 : ∀ P ∈ pathPatterns 0 1 [1, 4], HasCheckedCertificate 16 8 ([[], [1], [1], [1, 4]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k16t8p261, Certificates.k16t8p261_check⟩

private theorem k16t8_cover549 : ∀ P ∈ pathPatterns 0 0 [1, 5], HasCheckedCertificate 16 8 ([[], [1], [1], [1, 5]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k16t8p262, Certificates.k16t8p262_check⟩

private theorem k16t8_cover550 : ∀ P ∈ pathPatterns 1 4 [2], HasCheckedCertificate 16 8 ([[], [1], [1], [2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [2] [] ∧ LexLE [] [])) h)

private theorem k16t8_cover551 : ∀ P ∈ pathPatterns 0 2 [2, 2], HasCheckedCertificate 16 8 ([[], [1], [1], [2, 2]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k16t8p263, Certificates.k16t8p263_check⟩

private theorem k16t8_cover552 : ∀ P ∈ pathPatterns 0 1 [2, 3], HasCheckedCertificate 16 8 ([[], [1], [1], [2, 3]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k16t8p264, Certificates.k16t8p264_check⟩

private theorem k16t8_cover553 : ∀ P ∈ pathPatterns 0 0 [2, 4], HasCheckedCertificate 16 8 ([[], [1], [1], [2, 4]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k16t8p265, Certificates.k16t8p265_check⟩

private theorem k16t8_cover554 : ∀ P ∈ pathPatterns 1 3 [3], HasCheckedCertificate 16 8 ([[], [1], [1], [3]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [3] [] ∧ LexLE [] [])) h)

private theorem k16t8_cover555 : ∀ P ∈ pathPatterns 0 0 [3, 3], HasCheckedCertificate 16 8 ([[], [1], [1], [3, 3]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k16t8p266, Certificates.k16t8p266_check⟩

private theorem k16t8_cover556 : ∀ P ∈ pathPatterns 1 2 [4], HasCheckedCertificate 16 8 ([[], [1], [1], [4]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [4] [] ∧ LexLE [] [])) h)

private theorem k16t8_cover557 : ∀ P ∈ pathPatterns 1 1 [5], HasCheckedCertificate 16 8 ([[], [1], [1], [5]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [5] [] ∧ LexLE [] [])) h)

private theorem k16t8_cover558 : ∀ P ∈ pathPatterns 1 0 [6], HasCheckedCertificate 16 8 ([[], [1], [1], [6]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [6] [] ∧ LexLE [] [])) h)

private theorem k16t8_cover543 : ∀ P ∈ pathPatterns 3 6 [1], HasCheckedCertificate 16 8 ([[], [1], [1]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [1] [] ∧ LexLE [] [])) h)
      · intro q
        fin_cases q
        · exact by
            constructor
            · exact by
                intro _
                exact k16t8_cover544
            · intro q
              fin_cases q
              · exact by
                  intro _
                  exact k16t8_cover545
              · exact by
                  intro _
                  exact k16t8_cover546
              · exact by
                  intro _
                  exact k16t8_cover547
              · exact by
                  intro _
                  exact k16t8_cover548
              · exact by
                  intro _
                  exact k16t8_cover549
        · exact by
            constructor
            · exact by
                intro _
                exact k16t8_cover550
            · intro q
              fin_cases q
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [1] [2, 1] ∧ LexLE [2, 1] [1, 2])) h)
              · exact by
                  intro _
                  exact k16t8_cover551
              · exact by
                  intro _
                  exact k16t8_cover552
              · exact by
                  intro _
                  exact k16t8_cover553
        · exact by
            constructor
            · exact by
                intro _
                exact k16t8_cover554
            · intro q
              fin_cases q
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [1] [3, 1] ∧ LexLE [3, 1] [1, 3])) h)
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [1] [3, 2] ∧ LexLE [3, 2] [2, 3])) h)
              · exact by
                  intro _
                  exact k16t8_cover555
        · exact by
            constructor
            · exact by
                intro _
                exact k16t8_cover556
            · intro q
              fin_cases q
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [1] [4, 1] ∧ LexLE [4, 1] [1, 4])) h)
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [1] [4, 2] ∧ LexLE [4, 2] [2, 4])) h)
        · exact by
            constructor
            · exact by
                intro _
                exact k16t8_cover557
            · intro q
              fin_cases q
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [1] [5, 1] ∧ LexLE [5, 1] [1, 5])) h)
        · exact by
            constructor
            · exact by
                intro _
                exact k16t8_cover558
            · intro q
              exact Fin.elim0 q

private theorem k16t8_cover560 : ∀ P ∈ pathPatterns 0 3 [2], HasCheckedCertificate 16 8 ([[], [1], [1, 1], [2]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k16t8p267, Certificates.k16t8p267_check⟩

private theorem k16t8_cover561 : ∀ P ∈ pathPatterns 0 2 [3], HasCheckedCertificate 16 8 ([[], [1], [1, 1], [3]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k16t8p268, Certificates.k16t8p268_check⟩

private theorem k16t8_cover562 : ∀ P ∈ pathPatterns 0 1 [4], HasCheckedCertificate 16 8 ([[], [1], [1, 1], [4]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k16t8p269, Certificates.k16t8p269_check⟩

private theorem k16t8_cover563 : ∀ P ∈ pathPatterns 0 0 [5], HasCheckedCertificate 16 8 ([[], [1], [1, 1], [5]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k16t8p270, Certificates.k16t8p270_check⟩

private theorem k16t8_cover559 : ∀ P ∈ pathPatterns 2 5 [1, 1], HasCheckedCertificate 16 8 ([[], [1], [1, 1]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [1, 1] [] ∧ LexLE [] [])) h)
      · intro q
        fin_cases q
        · exact by
            intro h
            exact False.elim ((by decide : ¬ (LexLE [1, 1] [1] ∧ LexLE [1] [1])) h)
        · exact by
            intro _
            exact k16t8_cover560
        · exact by
            intro _
            exact k16t8_cover561
        · exact by
            intro _
            exact k16t8_cover562
        · exact by
            intro _
            exact k16t8_cover563

private theorem k16t8_cover564 : ∀ P ∈ pathPatterns 1 4 [1, 1, 1], HasCheckedCertificate 16 8 ([[], [1], [1, 1, 1]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [1, 1, 1] [] ∧ LexLE [] [])) h)

private theorem k16t8_cover565 : ∀ P ∈ pathPatterns 0 3 [1, 1, 1, 1], HasCheckedCertificate 16 8 ([[], [1], [1, 1, 1, 1]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k16t8p271, Certificates.k16t8p271_check⟩

private theorem k16t8_cover566 : ∀ P ∈ pathPatterns 0 2 [1, 1, 1, 2], HasCheckedCertificate 16 8 ([[], [1], [1, 1, 1, 2]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k16t8p272, Certificates.k16t8p272_check⟩

private theorem k16t8_cover567 : ∀ P ∈ pathPatterns 0 1 [1, 1, 1, 3], HasCheckedCertificate 16 8 ([[], [1], [1, 1, 1, 3]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k16t8p273, Certificates.k16t8p273_check⟩

private theorem k16t8_cover568 : ∀ P ∈ pathPatterns 0 0 [1, 1, 1, 4], HasCheckedCertificate 16 8 ([[], [1], [1, 1, 1, 4]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k16t8p274, Certificates.k16t8p274_check⟩

private theorem k16t8_cover569 : ∀ P ∈ pathPatterns 1 3 [1, 1, 2], HasCheckedCertificate 16 8 ([[], [1], [1, 1, 2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [1, 1, 2] [] ∧ LexLE [] [])) h)

private theorem k16t8_cover570 : ∀ P ∈ pathPatterns 0 2 [1, 1, 2, 1], HasCheckedCertificate 16 8 ([[], [1], [1, 1, 2, 1]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k16t8p275, Certificates.k16t8p275_check⟩

private theorem k16t8_cover571 : ∀ P ∈ pathPatterns 0 1 [1, 1, 2, 2], HasCheckedCertificate 16 8 ([[], [1], [1, 1, 2, 2]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k16t8p276, Certificates.k16t8p276_check⟩

private theorem k16t8_cover572 : ∀ P ∈ pathPatterns 0 0 [1, 1, 2, 3], HasCheckedCertificate 16 8 ([[], [1], [1, 1, 2, 3]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k16t8p277, Certificates.k16t8p277_check⟩

private theorem k16t8_cover573 : ∀ P ∈ pathPatterns 1 2 [1, 1, 3], HasCheckedCertificate 16 8 ([[], [1], [1, 1, 3]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [1, 1, 3] [] ∧ LexLE [] [])) h)

private theorem k16t8_cover574 : ∀ P ∈ pathPatterns 0 1 [1, 1, 3, 1], HasCheckedCertificate 16 8 ([[], [1], [1, 1, 3, 1]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k16t8p278, Certificates.k16t8p278_check⟩

private theorem k16t8_cover575 : ∀ P ∈ pathPatterns 0 0 [1, 1, 3, 2], HasCheckedCertificate 16 8 ([[], [1], [1, 1, 3, 2]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k16t8p279, Certificates.k16t8p279_check⟩

private theorem k16t8_cover576 : ∀ P ∈ pathPatterns 1 1 [1, 1, 4], HasCheckedCertificate 16 8 ([[], [1], [1, 1, 4]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [1, 1, 4] [] ∧ LexLE [] [])) h)

private theorem k16t8_cover577 : ∀ P ∈ pathPatterns 0 0 [1, 1, 4, 1], HasCheckedCertificate 16 8 ([[], [1], [1, 1, 4, 1]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k16t8p280, Certificates.k16t8p280_check⟩

private theorem k16t8_cover578 : ∀ P ∈ pathPatterns 1 0 [1, 1, 5], HasCheckedCertificate 16 8 ([[], [1], [1, 1, 5]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [1, 1, 5] [] ∧ LexLE [] [])) h)

private theorem k16t8_cover580 : ∀ P ∈ pathPatterns 0 2 [2], HasCheckedCertificate 16 8 ([[], [1], [1, 2], [2]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k16t8p281, Certificates.k16t8p281_check⟩

private theorem k16t8_cover581 : ∀ P ∈ pathPatterns 0 1 [3], HasCheckedCertificate 16 8 ([[], [1], [1, 2], [3]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k16t8p282, Certificates.k16t8p282_check⟩

private theorem k16t8_cover582 : ∀ P ∈ pathPatterns 0 0 [4], HasCheckedCertificate 16 8 ([[], [1], [1, 2], [4]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k16t8p283, Certificates.k16t8p283_check⟩

private theorem k16t8_cover579 : ∀ P ∈ pathPatterns 2 4 [1, 2], HasCheckedCertificate 16 8 ([[], [1], [1, 2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [1, 2] [] ∧ LexLE [] [])) h)
      · intro q
        fin_cases q
        · exact by
            intro h
            exact False.elim ((by decide : ¬ (LexLE [1, 2] [1] ∧ LexLE [1] [1])) h)
        · exact by
            intro _
            exact k16t8_cover580
        · exact by
            intro _
            exact k16t8_cover581
        · exact by
            intro _
            exact k16t8_cover582

private theorem k16t8_cover583 : ∀ P ∈ pathPatterns 1 3 [1, 2, 1], HasCheckedCertificate 16 8 ([[], [1], [1, 2, 1]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [1, 2, 1] [] ∧ LexLE [] [])) h)

private theorem k16t8_cover584 : ∀ P ∈ pathPatterns 0 1 [1, 2, 1, 2], HasCheckedCertificate 16 8 ([[], [1], [1, 2, 1, 2]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k16t8p284, Certificates.k16t8p284_check⟩

private theorem k16t8_cover585 : ∀ P ∈ pathPatterns 0 0 [1, 2, 1, 3], HasCheckedCertificate 16 8 ([[], [1], [1, 2, 1, 3]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k16t8p285, Certificates.k16t8p285_check⟩

private theorem k16t8_cover586 : ∀ P ∈ pathPatterns 1 2 [1, 2, 2], HasCheckedCertificate 16 8 ([[], [1], [1, 2, 2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [1, 2, 2] [] ∧ LexLE [] [])) h)

private theorem k16t8_cover587 : ∀ P ∈ pathPatterns 0 1 [1, 2, 2, 1], HasCheckedCertificate 16 8 ([[], [1], [1, 2, 2, 1]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k16t8p286, Certificates.k16t8p286_check⟩

private theorem k16t8_cover588 : ∀ P ∈ pathPatterns 0 0 [1, 2, 2, 2], HasCheckedCertificate 16 8 ([[], [1], [1, 2, 2, 2]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k16t8p287, Certificates.k16t8p287_check⟩

private theorem k16t8_cover589 : ∀ P ∈ pathPatterns 1 1 [1, 2, 3], HasCheckedCertificate 16 8 ([[], [1], [1, 2, 3]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [1, 2, 3] [] ∧ LexLE [] [])) h)

private theorem k16t8_cover590 : ∀ P ∈ pathPatterns 0 0 [1, 2, 3, 1], HasCheckedCertificate 16 8 ([[], [1], [1, 2, 3, 1]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k16t8p288, Certificates.k16t8p288_check⟩

private theorem k16t8_cover591 : ∀ P ∈ pathPatterns 1 0 [1, 2, 4], HasCheckedCertificate 16 8 ([[], [1], [1, 2, 4]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [1, 2, 4] [] ∧ LexLE [] [])) h)

private theorem k16t8_cover593 : ∀ P ∈ pathPatterns 0 1 [2], HasCheckedCertificate 16 8 ([[], [1], [1, 3], [2]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k16t8p289, Certificates.k16t8p289_check⟩

private theorem k16t8_cover594 : ∀ P ∈ pathPatterns 0 0 [3], HasCheckedCertificate 16 8 ([[], [1], [1, 3], [3]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k16t8p290, Certificates.k16t8p290_check⟩

private theorem k16t8_cover592 : ∀ P ∈ pathPatterns 2 3 [1, 3], HasCheckedCertificate 16 8 ([[], [1], [1, 3]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [1, 3] [] ∧ LexLE [] [])) h)
      · intro q
        fin_cases q
        · exact by
            intro h
            exact False.elim ((by decide : ¬ (LexLE [1, 3] [1] ∧ LexLE [1] [1])) h)
        · exact by
            intro _
            exact k16t8_cover593
        · exact by
            intro _
            exact k16t8_cover594

private theorem k16t8_cover595 : ∀ P ∈ pathPatterns 1 2 [1, 3, 1], HasCheckedCertificate 16 8 ([[], [1], [1, 3, 1]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [1, 3, 1] [] ∧ LexLE [] [])) h)

private theorem k16t8_cover596 : ∀ P ∈ pathPatterns 0 0 [1, 3, 1, 2], HasCheckedCertificate 16 8 ([[], [1], [1, 3, 1, 2]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k16t8p291, Certificates.k16t8p291_check⟩

private theorem k16t8_cover597 : ∀ P ∈ pathPatterns 1 1 [1, 3, 2], HasCheckedCertificate 16 8 ([[], [1], [1, 3, 2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [1, 3, 2] [] ∧ LexLE [] [])) h)

private theorem k16t8_cover598 : ∀ P ∈ pathPatterns 1 0 [1, 3, 3], HasCheckedCertificate 16 8 ([[], [1], [1, 3, 3]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [1, 3, 3] [] ∧ LexLE [] [])) h)

private theorem k16t8_cover600 : ∀ P ∈ pathPatterns 0 0 [2], HasCheckedCertificate 16 8 ([[], [1], [1, 4], [2]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k16t8p292, Certificates.k16t8p292_check⟩

private theorem k16t8_cover599 : ∀ P ∈ pathPatterns 2 2 [1, 4], HasCheckedCertificate 16 8 ([[], [1], [1, 4]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [1, 4] [] ∧ LexLE [] [])) h)
      · intro q
        fin_cases q
        · exact by
            intro h
            exact False.elim ((by decide : ¬ (LexLE [1, 4] [1] ∧ LexLE [1] [1])) h)
        · exact by
            intro _
            exact k16t8_cover600

private theorem k16t8_cover601 : ∀ P ∈ pathPatterns 1 1 [1, 4, 1], HasCheckedCertificate 16 8 ([[], [1], [1, 4, 1]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [1, 4, 1] [] ∧ LexLE [] [])) h)

private theorem k16t8_cover602 : ∀ P ∈ pathPatterns 1 0 [1, 4, 2], HasCheckedCertificate 16 8 ([[], [1], [1, 4, 2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [1, 4, 2] [] ∧ LexLE [] [])) h)

private theorem k16t8_cover603 : ∀ P ∈ pathPatterns 2 1 [1, 5], HasCheckedCertificate 16 8 ([[], [1], [1, 5]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [1, 5] [] ∧ LexLE [] [])) h)
      · intro q
        fin_cases q
        · exact by
            intro h
            exact False.elim ((by decide : ¬ (LexLE [1, 5] [1] ∧ LexLE [1] [1])) h)

private theorem k16t8_cover604 : ∀ P ∈ pathPatterns 1 0 [1, 5, 1], HasCheckedCertificate 16 8 ([[], [1], [1, 5, 1]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [1, 5, 1] [] ∧ LexLE [] [])) h)

private theorem k16t8_cover605 : ∀ P ∈ pathPatterns 2 0 [1, 6], HasCheckedCertificate 16 8 ([[], [1], [1, 6]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [1, 6] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k16t8_seq542 : amountSequenceForall 3 6 (fun tail =>
    (LexLE [1] ([1] ++ tail) ∧ LexLE ([1] ++ tail) ([1] ++ tail).reverse) →
    ∀ P ∈ pathPatterns (4 - ([1] ++ tail).length) (7 - ([1] ++ tail).sum) ([1] ++ tail),
      HasCheckedCertificate 16 8 ([[], [1]] ++ (([1] ++ tail) :: P))) :=
by
  constructor
  · exact by
      intro _
      exact k16t8_cover543
  · intro q
    fin_cases q
    · exact by
        constructor
        · exact by
            intro _
            exact k16t8_cover559
        · intro q
          fin_cases q
          · exact by
              constructor
              · exact by
                  intro _
                  exact k16t8_cover564
              · intro q
                fin_cases q
                · exact by
                    intro _
                    exact k16t8_cover565
                · exact by
                    intro _
                    exact k16t8_cover566
                · exact by
                    intro _
                    exact k16t8_cover567
                · exact by
                    intro _
                    exact k16t8_cover568
          · exact by
              constructor
              · exact by
                  intro _
                  exact k16t8_cover569
              · intro q
                fin_cases q
                · exact by
                    intro _
                    exact k16t8_cover570
                · exact by
                    intro _
                    exact k16t8_cover571
                · exact by
                    intro _
                    exact k16t8_cover572
          · exact by
              constructor
              · exact by
                  intro _
                  exact k16t8_cover573
              · intro q
                fin_cases q
                · exact by
                    intro _
                    exact k16t8_cover574
                · exact by
                    intro _
                    exact k16t8_cover575
          · exact by
              constructor
              · exact by
                  intro _
                  exact k16t8_cover576
              · intro q
                fin_cases q
                · exact by
                    intro _
                    exact k16t8_cover577
          · exact by
              constructor
              · exact by
                  intro _
                  exact k16t8_cover578
              · intro q
                exact Fin.elim0 q
    · exact by
        constructor
        · exact by
            intro _
            exact k16t8_cover579
        · intro q
          fin_cases q
          · exact by
              constructor
              · exact by
                  intro _
                  exact k16t8_cover583
              · intro q
                fin_cases q
                · exact by
                    intro h
                    exact False.elim ((by decide : ¬ (LexLE [1] [1, 2, 1, 1] ∧ LexLE [1, 2, 1, 1] [1, 1, 2, 1])) h)
                · exact by
                    intro _
                    exact k16t8_cover584
                · exact by
                    intro _
                    exact k16t8_cover585
          · exact by
              constructor
              · exact by
                  intro _
                  exact k16t8_cover586
              · intro q
                fin_cases q
                · exact by
                    intro _
                    exact k16t8_cover587
                · exact by
                    intro _
                    exact k16t8_cover588
          · exact by
              constructor
              · exact by
                  intro _
                  exact k16t8_cover589
              · intro q
                fin_cases q
                · exact by
                    intro _
                    exact k16t8_cover590
          · exact by
              constructor
              · exact by
                  intro _
                  exact k16t8_cover591
              · intro q
                exact Fin.elim0 q
    · exact by
        constructor
        · exact by
            intro _
            exact k16t8_cover592
        · intro q
          fin_cases q
          · exact by
              constructor
              · exact by
                  intro _
                  exact k16t8_cover595
              · intro q
                fin_cases q
                · exact by
                    intro h
                    exact False.elim ((by decide : ¬ (LexLE [1] [1, 3, 1, 1] ∧ LexLE [1, 3, 1, 1] [1, 1, 3, 1])) h)
                · exact by
                    intro _
                    exact k16t8_cover596
          · exact by
              constructor
              · exact by
                  intro _
                  exact k16t8_cover597
              · intro q
                fin_cases q
                · exact by
                    intro h
                    exact False.elim ((by decide : ¬ (LexLE [1] [1, 3, 2, 1] ∧ LexLE [1, 3, 2, 1] [1, 2, 3, 1])) h)
          · exact by
              constructor
              · exact by
                  intro _
                  exact k16t8_cover598
              · intro q
                exact Fin.elim0 q
    · exact by
        constructor
        · exact by
            intro _
            exact k16t8_cover599
        · intro q
          fin_cases q
          · exact by
              constructor
              · exact by
                  intro _
                  exact k16t8_cover601
              · intro q
                fin_cases q
                · exact by
                    intro h
                    exact False.elim ((by decide : ¬ (LexLE [1] [1, 4, 1, 1] ∧ LexLE [1, 4, 1, 1] [1, 1, 4, 1])) h)
          · exact by
              constructor
              · exact by
                  intro _
                  exact k16t8_cover602
              · intro q
                exact Fin.elim0 q
    · exact by
        constructor
        · exact by
            intro _
            exact k16t8_cover603
        · intro q
          fin_cases q
          · exact by
              constructor
              · exact by
                  intro _
                  exact k16t8_cover604
              · intro q
                exact Fin.elim0 q
    · exact by
        constructor
        · exact by
            intro _
            exact k16t8_cover605
        · intro q
          exact Fin.elim0 q

private theorem k16t8_cover608 : ∀ P ∈ pathPatterns 1 3 [2], HasCheckedCertificate 16 8 ([[], [1], [2], [2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [2] [] ∧ LexLE [] [])) h)

private theorem k16t8_cover609 : ∀ P ∈ pathPatterns 0 1 [2, 2], HasCheckedCertificate 16 8 ([[], [1], [2], [2, 2]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k16t8p293, Certificates.k16t8p293_check⟩

private theorem k16t8_cover610 : ∀ P ∈ pathPatterns 0 0 [2, 3], HasCheckedCertificate 16 8 ([[], [1], [2], [2, 3]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k16t8p294, Certificates.k16t8p294_check⟩

private theorem k16t8_cover611 : ∀ P ∈ pathPatterns 1 2 [3], HasCheckedCertificate 16 8 ([[], [1], [2], [3]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [3] [] ∧ LexLE [] [])) h)

private theorem k16t8_cover612 : ∀ P ∈ pathPatterns 1 1 [4], HasCheckedCertificate 16 8 ([[], [1], [2], [4]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [4] [] ∧ LexLE [] [])) h)

private theorem k16t8_cover613 : ∀ P ∈ pathPatterns 1 0 [5], HasCheckedCertificate 16 8 ([[], [1], [2], [5]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [5] [] ∧ LexLE [] [])) h)

private theorem k16t8_cover607 : ∀ P ∈ pathPatterns 3 5 [2], HasCheckedCertificate 16 8 ([[], [1], [2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [2] [] ∧ LexLE [] [])) h)
      · intro q
        fin_cases q
        · exact by
            constructor
            · exact by
                intro h
                exact False.elim ((by decide : ¬ (LexLE [2] [1] ∧ LexLE [1] [1])) h)
            · intro q
              fin_cases q
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [2] [1, 1] ∧ LexLE [1, 1] [1, 1])) h)
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [2] [1, 2] ∧ LexLE [1, 2] [2, 1])) h)
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [2] [1, 3] ∧ LexLE [1, 3] [3, 1])) h)
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [2] [1, 4] ∧ LexLE [1, 4] [4, 1])) h)
        · exact by
            constructor
            · exact by
                intro _
                exact k16t8_cover608
            · intro q
              fin_cases q
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [2] [2, 1] ∧ LexLE [2, 1] [1, 2])) h)
              · exact by
                  intro _
                  exact k16t8_cover609
              · exact by
                  intro _
                  exact k16t8_cover610
        · exact by
            constructor
            · exact by
                intro _
                exact k16t8_cover611
            · intro q
              fin_cases q
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [2] [3, 1] ∧ LexLE [3, 1] [1, 3])) h)
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [2] [3, 2] ∧ LexLE [3, 2] [2, 3])) h)
        · exact by
            constructor
            · exact by
                intro _
                exact k16t8_cover612
            · intro q
              fin_cases q
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [2] [4, 1] ∧ LexLE [4, 1] [1, 4])) h)
        · exact by
            constructor
            · exact by
                intro _
                exact k16t8_cover613
            · intro q
              exact Fin.elim0 q

private theorem k16t8_cover614 : ∀ P ∈ pathPatterns 0 1 [2, 1, 1, 2], HasCheckedCertificate 16 8 ([[], [1], [2, 1, 1, 2]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k16t8p295, Certificates.k16t8p295_check⟩

private theorem k16t8_cover615 : ∀ P ∈ pathPatterns 0 0 [2, 1, 1, 3], HasCheckedCertificate 16 8 ([[], [1], [2, 1, 1, 3]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k16t8p296, Certificates.k16t8p296_check⟩

private theorem k16t8_cover616 : ∀ P ∈ pathPatterns 1 2 [2, 1, 2], HasCheckedCertificate 16 8 ([[], [1], [2, 1, 2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [2, 1, 2] [] ∧ LexLE [] [])) h)

private theorem k16t8_cover617 : ∀ P ∈ pathPatterns 0 0 [2, 1, 2, 2], HasCheckedCertificate 16 8 ([[], [1], [2, 1, 2, 2]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k16t8p297, Certificates.k16t8p297_check⟩

private theorem k16t8_cover618 : ∀ P ∈ pathPatterns 1 1 [2, 1, 3], HasCheckedCertificate 16 8 ([[], [1], [2, 1, 3]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [2, 1, 3] [] ∧ LexLE [] [])) h)

private theorem k16t8_cover619 : ∀ P ∈ pathPatterns 1 0 [2, 1, 4], HasCheckedCertificate 16 8 ([[], [1], [2, 1, 4]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [2, 1, 4] [] ∧ LexLE [] [])) h)

private theorem k16t8_cover621 : ∀ P ∈ pathPatterns 0 0 [3], HasCheckedCertificate 16 8 ([[], [1], [2, 2], [3]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k16t8p298, Certificates.k16t8p298_check⟩

private theorem k16t8_cover620 : ∀ P ∈ pathPatterns 2 3 [2, 2], HasCheckedCertificate 16 8 ([[], [1], [2, 2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [2, 2] [] ∧ LexLE [] [])) h)
      · intro q
        fin_cases q
        · exact by
            intro h
            exact False.elim ((by decide : ¬ (LexLE [2, 2] [1] ∧ LexLE [1] [1])) h)
        · exact by
            intro h
            exact False.elim ((by decide : ¬ (LexLE [2, 2] [2] ∧ LexLE [2] [2])) h)
        · exact by
            intro _
            exact k16t8_cover621

private theorem k16t8_cover622 : ∀ P ∈ pathPatterns 1 1 [2, 2, 2], HasCheckedCertificate 16 8 ([[], [1], [2, 2, 2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [2, 2, 2] [] ∧ LexLE [] [])) h)

private theorem k16t8_cover623 : ∀ P ∈ pathPatterns 1 0 [2, 2, 3], HasCheckedCertificate 16 8 ([[], [1], [2, 2, 3]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [2, 2, 3] [] ∧ LexLE [] [])) h)

private theorem k16t8_cover624 : ∀ P ∈ pathPatterns 2 2 [2, 3], HasCheckedCertificate 16 8 ([[], [1], [2, 3]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [2, 3] [] ∧ LexLE [] [])) h)
      · intro q
        fin_cases q
        · exact by
            intro h
            exact False.elim ((by decide : ¬ (LexLE [2, 3] [1] ∧ LexLE [1] [1])) h)
        · exact by
            intro h
            exact False.elim ((by decide : ¬ (LexLE [2, 3] [2] ∧ LexLE [2] [2])) h)

private theorem k16t8_cover625 : ∀ P ∈ pathPatterns 1 0 [2, 3, 2], HasCheckedCertificate 16 8 ([[], [1], [2, 3, 2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [2, 3, 2] [] ∧ LexLE [] [])) h)

private theorem k16t8_cover626 : ∀ P ∈ pathPatterns 2 1 [2, 4], HasCheckedCertificate 16 8 ([[], [1], [2, 4]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [2, 4] [] ∧ LexLE [] [])) h)
      · intro q
        fin_cases q
        · exact by
            intro h
            exact False.elim ((by decide : ¬ (LexLE [2, 4] [1] ∧ LexLE [1] [1])) h)

private theorem k16t8_cover627 : ∀ P ∈ pathPatterns 2 0 [2, 5], HasCheckedCertificate 16 8 ([[], [1], [2, 5]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [2, 5] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k16t8_seq606 : amountSequenceForall 3 5 (fun tail =>
    (LexLE [1] ([2] ++ tail) ∧ LexLE ([2] ++ tail) ([2] ++ tail).reverse) →
    ∀ P ∈ pathPatterns (4 - ([2] ++ tail).length) (7 - ([2] ++ tail).sum) ([2] ++ tail),
      HasCheckedCertificate 16 8 ([[], [1]] ++ (([2] ++ tail) :: P))) :=
by
  constructor
  · exact by
      intro _
      exact k16t8_cover607
  · intro q
    fin_cases q
    · exact by
        constructor
        · exact by
            intro h
            exact False.elim ((by decide : ¬ (LexLE [1] [2, 1] ∧ LexLE [2, 1] [1, 2])) h)
        · intro q
          fin_cases q
          · exact by
              constructor
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [1] [2, 1, 1] ∧ LexLE [2, 1, 1] [1, 1, 2])) h)
              · intro q
                fin_cases q
                · exact by
                    intro h
                    exact False.elim ((by decide : ¬ (LexLE [1] [2, 1, 1, 1] ∧ LexLE [2, 1, 1, 1] [1, 1, 1, 2])) h)
                · exact by
                    intro _
                    exact k16t8_cover614
                · exact by
                    intro _
                    exact k16t8_cover615
          · exact by
              constructor
              · exact by
                  intro _
                  exact k16t8_cover616
              · intro q
                fin_cases q
                · exact by
                    intro h
                    exact False.elim ((by decide : ¬ (LexLE [1] [2, 1, 2, 1] ∧ LexLE [2, 1, 2, 1] [1, 2, 1, 2])) h)
                · exact by
                    intro _
                    exact k16t8_cover617
          · exact by
              constructor
              · exact by
                  intro _
                  exact k16t8_cover618
              · intro q
                fin_cases q
                · exact by
                    intro h
                    exact False.elim ((by decide : ¬ (LexLE [1] [2, 1, 3, 1] ∧ LexLE [2, 1, 3, 1] [1, 3, 1, 2])) h)
          · exact by
              constructor
              · exact by
                  intro _
                  exact k16t8_cover619
              · intro q
                exact Fin.elim0 q
    · exact by
        constructor
        · exact by
            intro _
            exact k16t8_cover620
        · intro q
          fin_cases q
          · exact by
              constructor
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [1] [2, 2, 1] ∧ LexLE [2, 2, 1] [1, 2, 2])) h)
              · intro q
                fin_cases q
                · exact by
                    intro h
                    exact False.elim ((by decide : ¬ (LexLE [1] [2, 2, 1, 1] ∧ LexLE [2, 2, 1, 1] [1, 1, 2, 2])) h)
                · exact by
                    intro h
                    exact False.elim ((by decide : ¬ (LexLE [1] [2, 2, 1, 2] ∧ LexLE [2, 2, 1, 2] [2, 1, 2, 2])) h)
          · exact by
              constructor
              · exact by
                  intro _
                  exact k16t8_cover622
              · intro q
                fin_cases q
                · exact by
                    intro h
                    exact False.elim ((by decide : ¬ (LexLE [1] [2, 2, 2, 1] ∧ LexLE [2, 2, 2, 1] [1, 2, 2, 2])) h)
          · exact by
              constructor
              · exact by
                  intro _
                  exact k16t8_cover623
              · intro q
                exact Fin.elim0 q
    · exact by
        constructor
        · exact by
            intro _
            exact k16t8_cover624
        · intro q
          fin_cases q
          · exact by
              constructor
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [1] [2, 3, 1] ∧ LexLE [2, 3, 1] [1, 3, 2])) h)
              · intro q
                fin_cases q
                · exact by
                    intro h
                    exact False.elim ((by decide : ¬ (LexLE [1] [2, 3, 1, 1] ∧ LexLE [2, 3, 1, 1] [1, 1, 3, 2])) h)
          · exact by
              constructor
              · exact by
                  intro _
                  exact k16t8_cover625
              · intro q
                exact Fin.elim0 q
    · exact by
        constructor
        · exact by
            intro _
            exact k16t8_cover626
        · intro q
          fin_cases q
          · exact by
              constructor
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [1] [2, 4, 1] ∧ LexLE [2, 4, 1] [1, 4, 2])) h)
              · intro q
                exact Fin.elim0 q
    · exact by
        constructor
        · exact by
            intro _
            exact k16t8_cover627
        · intro q
          exact Fin.elim0 q

private theorem k16t8_cover629 : ∀ P ∈ pathPatterns 1 1 [3], HasCheckedCertificate 16 8 ([[], [1], [3], [3]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [3] [] ∧ LexLE [] [])) h)

private theorem k16t8_cover630 : ∀ P ∈ pathPatterns 1 0 [4], HasCheckedCertificate 16 8 ([[], [1], [3], [4]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [4] [] ∧ LexLE [] [])) h)

private theorem k16t8_cover628 : ∀ P ∈ pathPatterns 3 4 [3], HasCheckedCertificate 16 8 ([[], [1], [3]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [3] [] ∧ LexLE [] [])) h)
      · intro q
        fin_cases q
        · exact by
            constructor
            · exact by
                intro h
                exact False.elim ((by decide : ¬ (LexLE [3] [1] ∧ LexLE [1] [1])) h)
            · intro q
              fin_cases q
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [3] [1, 1] ∧ LexLE [1, 1] [1, 1])) h)
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [3] [1, 2] ∧ LexLE [1, 2] [2, 1])) h)
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [3] [1, 3] ∧ LexLE [1, 3] [3, 1])) h)
        · exact by
            constructor
            · exact by
                intro h
                exact False.elim ((by decide : ¬ (LexLE [3] [2] ∧ LexLE [2] [2])) h)
            · intro q
              fin_cases q
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [3] [2, 1] ∧ LexLE [2, 1] [1, 2])) h)
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [3] [2, 2] ∧ LexLE [2, 2] [2, 2])) h)
        · exact by
            constructor
            · exact by
                intro _
                exact k16t8_cover629
            · intro q
              fin_cases q
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [3] [3, 1] ∧ LexLE [3, 1] [1, 3])) h)
        · exact by
            constructor
            · exact by
                intro _
                exact k16t8_cover630
            · intro q
              exact Fin.elim0 q

private theorem k16t8_cover631 : ∀ P ∈ pathPatterns 1 0 [3, 1, 3], HasCheckedCertificate 16 8 ([[], [1], [3, 1, 3]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [3, 1, 3] [] ∧ LexLE [] [])) h)

private theorem k16t8_cover632 : ∀ P ∈ pathPatterns 2 1 [3, 3], HasCheckedCertificate 16 8 ([[], [1], [3, 3]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [3, 3] [] ∧ LexLE [] [])) h)
      · intro q
        fin_cases q
        · exact by
            intro h
            exact False.elim ((by decide : ¬ (LexLE [3, 3] [1] ∧ LexLE [1] [1])) h)

private theorem k16t8_cover633 : ∀ P ∈ pathPatterns 2 0 [3, 4], HasCheckedCertificate 16 8 ([[], [1], [3, 4]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [3, 4] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k16t8_cover634 : ∀ P ∈ pathPatterns 3 3 [4], HasCheckedCertificate 16 8 ([[], [1], [4]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [4] [] ∧ LexLE [] [])) h)
      · intro q
        fin_cases q
        · exact by
            constructor
            · exact by
                intro h
                exact False.elim ((by decide : ¬ (LexLE [4] [1] ∧ LexLE [1] [1])) h)
            · intro q
              fin_cases q
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [4] [1, 1] ∧ LexLE [1, 1] [1, 1])) h)
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [4] [1, 2] ∧ LexLE [1, 2] [2, 1])) h)
        · exact by
            constructor
            · exact by
                intro h
                exact False.elim ((by decide : ¬ (LexLE [4] [2] ∧ LexLE [2] [2])) h)
            · intro q
              fin_cases q
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [4] [2, 1] ∧ LexLE [2, 1] [1, 2])) h)
        · exact by
            constructor
            · exact by
                intro h
                exact False.elim ((by decide : ¬ (LexLE [4] [3] ∧ LexLE [3] [3])) h)
            · intro q
              exact Fin.elim0 q

private theorem k16t8_cover635 : ∀ P ∈ pathPatterns 3 2 [5], HasCheckedCertificate 16 8 ([[], [1], [5]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [5] [] ∧ LexLE [] [])) h)
      · intro q
        fin_cases q
        · exact by
            constructor
            · exact by
                intro h
                exact False.elim ((by decide : ¬ (LexLE [5] [1] ∧ LexLE [1] [1])) h)
            · intro q
              fin_cases q
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [5] [1, 1] ∧ LexLE [1, 1] [1, 1])) h)
        · exact by
            constructor
            · exact by
                intro h
                exact False.elim ((by decide : ¬ (LexLE [5] [2] ∧ LexLE [2] [2])) h)
            · intro q
              exact Fin.elim0 q

private theorem k16t8_cover636 : ∀ P ∈ pathPatterns 3 1 [6], HasCheckedCertificate 16 8 ([[], [1], [6]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [6] [] ∧ LexLE [] [])) h)
      · intro q
        fin_cases q
        · exact by
            constructor
            · exact by
                intro h
                exact False.elim ((by decide : ¬ (LexLE [6] [1] ∧ LexLE [1] [1])) h)
            · intro q
              exact Fin.elim0 q

private theorem k16t8_cover637 : ∀ P ∈ pathPatterns 3 0 [7], HasCheckedCertificate 16 8 ([[], [1], [7]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [7] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k16t8_seq541 : amountSequenceForall 4 7 (fun tail =>
    (LexLE [1] ([] ++ tail) ∧ LexLE ([] ++ tail) ([] ++ tail).reverse) →
    ∀ P ∈ pathPatterns (4 - ([] ++ tail).length) (7 - ([] ++ tail).sum) ([] ++ tail),
      HasCheckedCertificate 16 8 ([[], [1]] ++ (([] ++ tail) :: P))) :=
by
  constructor
  · exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [1] [] ∧ LexLE [] [])) h)
  · intro q
    fin_cases q
    · exact k16t8_seq542

    · exact k16t8_seq606

    · exact by
        constructor
        · exact by
            intro _
            exact k16t8_cover628
        · intro q
          fin_cases q
          · exact by
              constructor
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [1] [3, 1] ∧ LexLE [3, 1] [1, 3])) h)
              · intro q
                fin_cases q
                · exact by
                    constructor
                    · exact by
                        intro h
                        exact False.elim ((by decide : ¬ (LexLE [1] [3, 1, 1] ∧ LexLE [3, 1, 1] [1, 1, 3])) h)
                    · intro q
                      fin_cases q
                      · exact by
                          intro h
                          exact False.elim ((by decide : ¬ (LexLE [1] [3, 1, 1, 1] ∧ LexLE [3, 1, 1, 1] [1, 1, 1, 3])) h)
                      · exact by
                          intro h
                          exact False.elim ((by decide : ¬ (LexLE [1] [3, 1, 1, 2] ∧ LexLE [3, 1, 1, 2] [2, 1, 1, 3])) h)
                · exact by
                    constructor
                    · exact by
                        intro h
                        exact False.elim ((by decide : ¬ (LexLE [1] [3, 1, 2] ∧ LexLE [3, 1, 2] [2, 1, 3])) h)
                    · intro q
                      fin_cases q
                      · exact by
                          intro h
                          exact False.elim ((by decide : ¬ (LexLE [1] [3, 1, 2, 1] ∧ LexLE [3, 1, 2, 1] [1, 2, 1, 3])) h)
                · exact by
                    constructor
                    · exact by
                        intro _
                        exact k16t8_cover631
                    · intro q
                      exact Fin.elim0 q
          · exact by
              constructor
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [1] [3, 2] ∧ LexLE [3, 2] [2, 3])) h)
              · intro q
                fin_cases q
                · exact by
                    constructor
                    · exact by
                        intro h
                        exact False.elim ((by decide : ¬ (LexLE [1] [3, 2, 1] ∧ LexLE [3, 2, 1] [1, 2, 3])) h)
                    · intro q
                      fin_cases q
                      · exact by
                          intro h
                          exact False.elim ((by decide : ¬ (LexLE [1] [3, 2, 1, 1] ∧ LexLE [3, 2, 1, 1] [1, 1, 2, 3])) h)
                · exact by
                    constructor
                    · exact by
                        intro h
                        exact False.elim ((by decide : ¬ (LexLE [1] [3, 2, 2] ∧ LexLE [3, 2, 2] [2, 2, 3])) h)
                    · intro q
                      exact Fin.elim0 q
          · exact by
              constructor
              · exact by
                  intro _
                  exact k16t8_cover632
              · intro q
                fin_cases q
                · exact by
                    constructor
                    · exact by
                        intro h
                        exact False.elim ((by decide : ¬ (LexLE [1] [3, 3, 1] ∧ LexLE [3, 3, 1] [1, 3, 3])) h)
                    · intro q
                      exact Fin.elim0 q
          · exact by
              constructor
              · exact by
                  intro _
                  exact k16t8_cover633
              · intro q
                exact Fin.elim0 q
    · exact by
        constructor
        · exact by
            intro _
            exact k16t8_cover634
        · intro q
          fin_cases q
          · exact by
              constructor
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [1] [4, 1] ∧ LexLE [4, 1] [1, 4])) h)
              · intro q
                fin_cases q
                · exact by
                    constructor
                    · exact by
                        intro h
                        exact False.elim ((by decide : ¬ (LexLE [1] [4, 1, 1] ∧ LexLE [4, 1, 1] [1, 1, 4])) h)
                    · intro q
                      fin_cases q
                      · exact by
                          intro h
                          exact False.elim ((by decide : ¬ (LexLE [1] [4, 1, 1, 1] ∧ LexLE [4, 1, 1, 1] [1, 1, 1, 4])) h)
                · exact by
                    constructor
                    · exact by
                        intro h
                        exact False.elim ((by decide : ¬ (LexLE [1] [4, 1, 2] ∧ LexLE [4, 1, 2] [2, 1, 4])) h)
                    · intro q
                      exact Fin.elim0 q
          · exact by
              constructor
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [1] [4, 2] ∧ LexLE [4, 2] [2, 4])) h)
              · intro q
                fin_cases q
                · exact by
                    constructor
                    · exact by
                        intro h
                        exact False.elim ((by decide : ¬ (LexLE [1] [4, 2, 1] ∧ LexLE [4, 2, 1] [1, 2, 4])) h)
                    · intro q
                      exact Fin.elim0 q
          · exact by
              constructor
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [1] [4, 3] ∧ LexLE [4, 3] [3, 4])) h)
              · intro q
                exact Fin.elim0 q
    · exact by
        constructor
        · exact by
            intro _
            exact k16t8_cover635
        · intro q
          fin_cases q
          · exact by
              constructor
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [1] [5, 1] ∧ LexLE [5, 1] [1, 5])) h)
              · intro q
                fin_cases q
                · exact by
                    constructor
                    · exact by
                        intro h
                        exact False.elim ((by decide : ¬ (LexLE [1] [5, 1, 1] ∧ LexLE [5, 1, 1] [1, 1, 5])) h)
                    · intro q
                      exact Fin.elim0 q
          · exact by
              constructor
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [1] [5, 2] ∧ LexLE [5, 2] [2, 5])) h)
              · intro q
                exact Fin.elim0 q
    · exact by
        constructor
        · exact by
            intro _
            exact k16t8_cover636
        · intro q
          fin_cases q
          · exact by
              constructor
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [1] [6, 1] ∧ LexLE [6, 1] [1, 6])) h)
              · intro q
                exact Fin.elim0 q
    · exact by
        constructor
        · exact by
            intro _
            exact k16t8_cover637
        · intro q
          exact Fin.elim0 q

private theorem k16t8_cover540 : ∀ P ∈ pathPatterns 5 7 [1], HasCheckedCertificate 16 8 ([[], [1]] ++ P) := by
  apply pathPatterns_forall_step
  exact k16t8_seq541


private theorem k16t8_cover641 : ∀ P ∈ pathPatterns 1 4 [1, 1], HasCheckedCertificate 16 8 ([[], [1, 1], [1, 1]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [1, 1] [] ∧ LexLE [] [])) h)

private theorem k16t8_cover642 : ∀ P ∈ pathPatterns 0 3 [1, 1, 1], HasCheckedCertificate 16 8 ([[], [1, 1], [1, 1, 1]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k16t8p299, Certificates.k16t8p299_check⟩

private theorem k16t8_cover643 : ∀ P ∈ pathPatterns 0 2 [1, 1, 2], HasCheckedCertificate 16 8 ([[], [1, 1], [1, 1, 2]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k16t8p300, Certificates.k16t8p300_check⟩

private theorem k16t8_cover644 : ∀ P ∈ pathPatterns 0 1 [1, 1, 3], HasCheckedCertificate 16 8 ([[], [1, 1], [1, 1, 3]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k16t8p301, Certificates.k16t8p301_check⟩

private theorem k16t8_cover645 : ∀ P ∈ pathPatterns 0 0 [1, 1, 4], HasCheckedCertificate 16 8 ([[], [1, 1], [1, 1, 4]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k16t8p302, Certificates.k16t8p302_check⟩

private theorem k16t8_cover646 : ∀ P ∈ pathPatterns 1 3 [1, 2], HasCheckedCertificate 16 8 ([[], [1, 1], [1, 2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [1, 2] [] ∧ LexLE [] [])) h)

private theorem k16t8_cover647 : ∀ P ∈ pathPatterns 0 2 [1, 2, 1], HasCheckedCertificate 16 8 ([[], [1, 1], [1, 2, 1]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k16t8p303, Certificates.k16t8p303_check⟩

private theorem k16t8_cover648 : ∀ P ∈ pathPatterns 0 1 [1, 2, 2], HasCheckedCertificate 16 8 ([[], [1, 1], [1, 2, 2]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k16t8p304, Certificates.k16t8p304_check⟩

private theorem k16t8_cover649 : ∀ P ∈ pathPatterns 0 0 [1, 2, 3], HasCheckedCertificate 16 8 ([[], [1, 1], [1, 2, 3]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k16t8p305, Certificates.k16t8p305_check⟩

private theorem k16t8_cover650 : ∀ P ∈ pathPatterns 1 2 [1, 3], HasCheckedCertificate 16 8 ([[], [1, 1], [1, 3]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [1, 3] [] ∧ LexLE [] [])) h)

private theorem k16t8_cover651 : ∀ P ∈ pathPatterns 0 1 [1, 3, 1], HasCheckedCertificate 16 8 ([[], [1, 1], [1, 3, 1]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k16t8p306, Certificates.k16t8p306_check⟩

private theorem k16t8_cover652 : ∀ P ∈ pathPatterns 0 0 [1, 3, 2], HasCheckedCertificate 16 8 ([[], [1, 1], [1, 3, 2]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k16t8p307, Certificates.k16t8p307_check⟩

private theorem k16t8_cover653 : ∀ P ∈ pathPatterns 1 1 [1, 4], HasCheckedCertificate 16 8 ([[], [1, 1], [1, 4]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [1, 4] [] ∧ LexLE [] [])) h)

private theorem k16t8_cover654 : ∀ P ∈ pathPatterns 0 0 [1, 4, 1], HasCheckedCertificate 16 8 ([[], [1, 1], [1, 4, 1]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k16t8p308, Certificates.k16t8p308_check⟩

private theorem k16t8_cover655 : ∀ P ∈ pathPatterns 1 0 [1, 5], HasCheckedCertificate 16 8 ([[], [1, 1], [1, 5]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [1, 5] [] ∧ LexLE [] [])) h)

private theorem k16t8_cover657 : ∀ P ∈ pathPatterns 0 2 [2], HasCheckedCertificate 16 8 ([[], [1, 1], [2], [2]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k16t8p309, Certificates.k16t8p309_check⟩

private theorem k16t8_cover658 : ∀ P ∈ pathPatterns 0 1 [3], HasCheckedCertificate 16 8 ([[], [1, 1], [2], [3]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k16t8p310, Certificates.k16t8p310_check⟩

private theorem k16t8_cover659 : ∀ P ∈ pathPatterns 0 0 [4], HasCheckedCertificate 16 8 ([[], [1, 1], [2], [4]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k16t8p311, Certificates.k16t8p311_check⟩

private theorem k16t8_cover656 : ∀ P ∈ pathPatterns 2 4 [2], HasCheckedCertificate 16 8 ([[], [1, 1], [2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [2] [] ∧ LexLE [] [])) h)
      · intro q
        fin_cases q
        · exact by
            intro h
            exact False.elim ((by decide : ¬ (LexLE [2] [1] ∧ LexLE [1] [1])) h)
        · exact by
            intro _
            exact k16t8_cover657
        · exact by
            intro _
            exact k16t8_cover658
        · exact by
            intro _
            exact k16t8_cover659

private theorem k16t8_cover660 : ∀ P ∈ pathPatterns 0 1 [2, 1, 2], HasCheckedCertificate 16 8 ([[], [1, 1], [2, 1, 2]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k16t8p312, Certificates.k16t8p312_check⟩

private theorem k16t8_cover661 : ∀ P ∈ pathPatterns 0 0 [2, 1, 3], HasCheckedCertificate 16 8 ([[], [1, 1], [2, 1, 3]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k16t8p313, Certificates.k16t8p313_check⟩

private theorem k16t8_cover662 : ∀ P ∈ pathPatterns 1 2 [2, 2], HasCheckedCertificate 16 8 ([[], [1, 1], [2, 2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [2, 2] [] ∧ LexLE [] [])) h)

private theorem k16t8_cover663 : ∀ P ∈ pathPatterns 0 0 [2, 2, 2], HasCheckedCertificate 16 8 ([[], [1, 1], [2, 2, 2]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k16t8p314, Certificates.k16t8p314_check⟩

private theorem k16t8_cover664 : ∀ P ∈ pathPatterns 1 1 [2, 3], HasCheckedCertificate 16 8 ([[], [1, 1], [2, 3]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [2, 3] [] ∧ LexLE [] [])) h)

private theorem k16t8_cover665 : ∀ P ∈ pathPatterns 1 0 [2, 4], HasCheckedCertificate 16 8 ([[], [1, 1], [2, 4]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [2, 4] [] ∧ LexLE [] [])) h)

private theorem k16t8_cover667 : ∀ P ∈ pathPatterns 0 0 [3], HasCheckedCertificate 16 8 ([[], [1, 1], [3], [3]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k16t8p315, Certificates.k16t8p315_check⟩

private theorem k16t8_cover666 : ∀ P ∈ pathPatterns 2 3 [3], HasCheckedCertificate 16 8 ([[], [1, 1], [3]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [3] [] ∧ LexLE [] [])) h)
      · intro q
        fin_cases q
        · exact by
            intro h
            exact False.elim ((by decide : ¬ (LexLE [3] [1] ∧ LexLE [1] [1])) h)
        · exact by
            intro h
            exact False.elim ((by decide : ¬ (LexLE [3] [2] ∧ LexLE [2] [2])) h)
        · exact by
            intro _
            exact k16t8_cover667

private theorem k16t8_cover668 : ∀ P ∈ pathPatterns 1 0 [3, 3], HasCheckedCertificate 16 8 ([[], [1, 1], [3, 3]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [3, 3] [] ∧ LexLE [] [])) h)

private theorem k16t8_cover669 : ∀ P ∈ pathPatterns 2 2 [4], HasCheckedCertificate 16 8 ([[], [1, 1], [4]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [4] [] ∧ LexLE [] [])) h)
      · intro q
        fin_cases q
        · exact by
            intro h
            exact False.elim ((by decide : ¬ (LexLE [4] [1] ∧ LexLE [1] [1])) h)
        · exact by
            intro h
            exact False.elim ((by decide : ¬ (LexLE [4] [2] ∧ LexLE [2] [2])) h)

private theorem k16t8_cover670 : ∀ P ∈ pathPatterns 2 1 [5], HasCheckedCertificate 16 8 ([[], [1, 1], [5]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [5] [] ∧ LexLE [] [])) h)
      · intro q
        fin_cases q
        · exact by
            intro h
            exact False.elim ((by decide : ¬ (LexLE [5] [1] ∧ LexLE [1] [1])) h)

private theorem k16t8_cover671 : ∀ P ∈ pathPatterns 2 0 [6], HasCheckedCertificate 16 8 ([[], [1, 1], [6]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [6] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k16t8_seq640 : amountSequenceForall 3 6 (fun tail =>
    (LexLE [1, 1] ([] ++ tail) ∧ LexLE ([] ++ tail) ([] ++ tail).reverse) →
    ∀ P ∈ pathPatterns (3 - ([] ++ tail).length) (6 - ([] ++ tail).sum) ([] ++ tail),
      HasCheckedCertificate 16 8 ([[], [1, 1]] ++ (([] ++ tail) :: P))) :=
by
  constructor
  · exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [1, 1] [] ∧ LexLE [] [])) h)
  · intro q
    fin_cases q
    · exact by
        constructor
        · exact by
            intro h
            exact False.elim ((by decide : ¬ (LexLE [1, 1] [1] ∧ LexLE [1] [1])) h)
        · intro q
          fin_cases q
          · exact by
              constructor
              · exact by
                  intro _
                  exact k16t8_cover641
              · intro q
                fin_cases q
                · exact by
                    intro _
                    exact k16t8_cover642
                · exact by
                    intro _
                    exact k16t8_cover643
                · exact by
                    intro _
                    exact k16t8_cover644
                · exact by
                    intro _
                    exact k16t8_cover645
          · exact by
              constructor
              · exact by
                  intro _
                  exact k16t8_cover646
              · intro q
                fin_cases q
                · exact by
                    intro _
                    exact k16t8_cover647
                · exact by
                    intro _
                    exact k16t8_cover648
                · exact by
                    intro _
                    exact k16t8_cover649
          · exact by
              constructor
              · exact by
                  intro _
                  exact k16t8_cover650
              · intro q
                fin_cases q
                · exact by
                    intro _
                    exact k16t8_cover651
                · exact by
                    intro _
                    exact k16t8_cover652
          · exact by
              constructor
              · exact by
                  intro _
                  exact k16t8_cover653
              · intro q
                fin_cases q
                · exact by
                    intro _
                    exact k16t8_cover654
          · exact by
              constructor
              · exact by
                  intro _
                  exact k16t8_cover655
              · intro q
                exact Fin.elim0 q
    · exact by
        constructor
        · exact by
            intro _
            exact k16t8_cover656
        · intro q
          fin_cases q
          · exact by
              constructor
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [1, 1] [2, 1] ∧ LexLE [2, 1] [1, 2])) h)
              · intro q
                fin_cases q
                · exact by
                    intro h
                    exact False.elim ((by decide : ¬ (LexLE [1, 1] [2, 1, 1] ∧ LexLE [2, 1, 1] [1, 1, 2])) h)
                · exact by
                    intro _
                    exact k16t8_cover660
                · exact by
                    intro _
                    exact k16t8_cover661
          · exact by
              constructor
              · exact by
                  intro _
                  exact k16t8_cover662
              · intro q
                fin_cases q
                · exact by
                    intro h
                    exact False.elim ((by decide : ¬ (LexLE [1, 1] [2, 2, 1] ∧ LexLE [2, 2, 1] [1, 2, 2])) h)
                · exact by
                    intro _
                    exact k16t8_cover663
          · exact by
              constructor
              · exact by
                  intro _
                  exact k16t8_cover664
              · intro q
                fin_cases q
                · exact by
                    intro h
                    exact False.elim ((by decide : ¬ (LexLE [1, 1] [2, 3, 1] ∧ LexLE [2, 3, 1] [1, 3, 2])) h)
          · exact by
              constructor
              · exact by
                  intro _
                  exact k16t8_cover665
              · intro q
                exact Fin.elim0 q
    · exact by
        constructor
        · exact by
            intro _
            exact k16t8_cover666
        · intro q
          fin_cases q
          · exact by
              constructor
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [1, 1] [3, 1] ∧ LexLE [3, 1] [1, 3])) h)
              · intro q
                fin_cases q
                · exact by
                    intro h
                    exact False.elim ((by decide : ¬ (LexLE [1, 1] [3, 1, 1] ∧ LexLE [3, 1, 1] [1, 1, 3])) h)
                · exact by
                    intro h
                    exact False.elim ((by decide : ¬ (LexLE [1, 1] [3, 1, 2] ∧ LexLE [3, 1, 2] [2, 1, 3])) h)
          · exact by
              constructor
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [1, 1] [3, 2] ∧ LexLE [3, 2] [2, 3])) h)
              · intro q
                fin_cases q
                · exact by
                    intro h
                    exact False.elim ((by decide : ¬ (LexLE [1, 1] [3, 2, 1] ∧ LexLE [3, 2, 1] [1, 2, 3])) h)
          · exact by
              constructor
              · exact by
                  intro _
                  exact k16t8_cover668
              · intro q
                exact Fin.elim0 q
    · exact by
        constructor
        · exact by
            intro _
            exact k16t8_cover669
        · intro q
          fin_cases q
          · exact by
              constructor
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [1, 1] [4, 1] ∧ LexLE [4, 1] [1, 4])) h)
              · intro q
                fin_cases q
                · exact by
                    intro h
                    exact False.elim ((by decide : ¬ (LexLE [1, 1] [4, 1, 1] ∧ LexLE [4, 1, 1] [1, 1, 4])) h)
          · exact by
              constructor
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [1, 1] [4, 2] ∧ LexLE [4, 2] [2, 4])) h)
              · intro q
                exact Fin.elim0 q
    · exact by
        constructor
        · exact by
            intro _
            exact k16t8_cover670
        · intro q
          fin_cases q
          · exact by
              constructor
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [1, 1] [5, 1] ∧ LexLE [5, 1] [1, 5])) h)
              · intro q
                exact Fin.elim0 q
    · exact by
        constructor
        · exact by
            intro _
            exact k16t8_cover671
        · intro q
          exact Fin.elim0 q

private theorem k16t8_cover639 : ∀ P ∈ pathPatterns 4 6 [1, 1], HasCheckedCertificate 16 8 ([[], [1, 1]] ++ P) := by
  apply pathPatterns_forall_step
  exact k16t8_seq640


private theorem k16t8_cover674 : ∀ P ∈ pathPatterns 0 2 [1, 2], HasCheckedCertificate 16 8 ([[], [1, 1, 1], [1, 2]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k16t8p316, Certificates.k16t8p316_check⟩

private theorem k16t8_cover675 : ∀ P ∈ pathPatterns 0 1 [1, 3], HasCheckedCertificate 16 8 ([[], [1, 1, 1], [1, 3]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k16t8p317, Certificates.k16t8p317_check⟩

private theorem k16t8_cover676 : ∀ P ∈ pathPatterns 0 0 [1, 4], HasCheckedCertificate 16 8 ([[], [1, 1, 1], [1, 4]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k16t8p318, Certificates.k16t8p318_check⟩

private theorem k16t8_cover677 : ∀ P ∈ pathPatterns 1 3 [2], HasCheckedCertificate 16 8 ([[], [1, 1, 1], [2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [2] [] ∧ LexLE [] [])) h)

private theorem k16t8_cover678 : ∀ P ∈ pathPatterns 0 1 [2, 2], HasCheckedCertificate 16 8 ([[], [1, 1, 1], [2, 2]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k16t8p319, Certificates.k16t8p319_check⟩

private theorem k16t8_cover679 : ∀ P ∈ pathPatterns 0 0 [2, 3], HasCheckedCertificate 16 8 ([[], [1, 1, 1], [2, 3]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k16t8p320, Certificates.k16t8p320_check⟩

private theorem k16t8_cover680 : ∀ P ∈ pathPatterns 1 2 [3], HasCheckedCertificate 16 8 ([[], [1, 1, 1], [3]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [3] [] ∧ LexLE [] [])) h)

private theorem k16t8_cover681 : ∀ P ∈ pathPatterns 1 1 [4], HasCheckedCertificate 16 8 ([[], [1, 1, 1], [4]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [4] [] ∧ LexLE [] [])) h)

private theorem k16t8_cover682 : ∀ P ∈ pathPatterns 1 0 [5], HasCheckedCertificate 16 8 ([[], [1, 1, 1], [5]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [5] [] ∧ LexLE [] [])) h)

private theorem k16t8_cover673 : ∀ P ∈ pathPatterns 3 5 [1, 1, 1], HasCheckedCertificate 16 8 ([[], [1, 1, 1]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [1, 1, 1] [] ∧ LexLE [] [])) h)
      · intro q
        fin_cases q
        · exact by
            constructor
            · exact by
                intro h
                exact False.elim ((by decide : ¬ (LexLE [1, 1, 1] [1] ∧ LexLE [1] [1])) h)
            · intro q
              fin_cases q
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [1, 1, 1] [1, 1] ∧ LexLE [1, 1] [1, 1])) h)
              · exact by
                  intro _
                  exact k16t8_cover674
              · exact by
                  intro _
                  exact k16t8_cover675
              · exact by
                  intro _
                  exact k16t8_cover676
        · exact by
            constructor
            · exact by
                intro _
                exact k16t8_cover677
            · intro q
              fin_cases q
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [1, 1, 1] [2, 1] ∧ LexLE [2, 1] [1, 2])) h)
              · exact by
                  intro _
                  exact k16t8_cover678
              · exact by
                  intro _
                  exact k16t8_cover679
        · exact by
            constructor
            · exact by
                intro _
                exact k16t8_cover680
            · intro q
              fin_cases q
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [1, 1, 1] [3, 1] ∧ LexLE [3, 1] [1, 3])) h)
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [1, 1, 1] [3, 2] ∧ LexLE [3, 2] [2, 3])) h)
        · exact by
            constructor
            · exact by
                intro _
                exact k16t8_cover681
            · intro q
              fin_cases q
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [1, 1, 1] [4, 1] ∧ LexLE [4, 1] [1, 4])) h)
        · exact by
            constructor
            · exact by
                intro _
                exact k16t8_cover682
            · intro q
              exact Fin.elim0 q

private theorem k16t8_cover684 : ∀ P ∈ pathPatterns 0 2 [2], HasCheckedCertificate 16 8 ([[], [1, 1, 1, 1], [2]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k16t8p321, Certificates.k16t8p321_check⟩

private theorem k16t8_cover685 : ∀ P ∈ pathPatterns 0 1 [3], HasCheckedCertificate 16 8 ([[], [1, 1, 1, 1], [3]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k16t8p322, Certificates.k16t8p322_check⟩

private theorem k16t8_cover686 : ∀ P ∈ pathPatterns 0 0 [4], HasCheckedCertificate 16 8 ([[], [1, 1, 1, 1], [4]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k16t8p323, Certificates.k16t8p323_check⟩

private theorem k16t8_cover683 : ∀ P ∈ pathPatterns 2 4 [1, 1, 1, 1], HasCheckedCertificate 16 8 ([[], [1, 1, 1, 1]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [1, 1, 1, 1] [] ∧ LexLE [] [])) h)
      · intro q
        fin_cases q
        · exact by
            intro h
            exact False.elim ((by decide : ¬ (LexLE [1, 1, 1, 1] [1] ∧ LexLE [1] [1])) h)
        · exact by
            intro _
            exact k16t8_cover684
        · exact by
            intro _
            exact k16t8_cover685
        · exact by
            intro _
            exact k16t8_cover686

private theorem k16t8_cover687 : ∀ P ∈ pathPatterns 1 3 [1, 1, 1, 1, 1], HasCheckedCertificate 16 8 ([[], [1, 1, 1, 1, 1]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [1, 1, 1, 1, 1] [] ∧ LexLE [] [])) h)

private theorem k16t8_cover688 : ∀ P ∈ pathPatterns 0 2 [1, 1, 1, 1, 1, 1], HasCheckedCertificate 16 8 ([[], [1, 1, 1, 1, 1, 1]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k16t8p324, Certificates.k16t8p324_check⟩

private theorem k16t8_cover689 : ∀ P ∈ pathPatterns 0 1 [1, 1, 1, 1, 1, 2], HasCheckedCertificate 16 8 ([[], [1, 1, 1, 1, 1, 2]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k16t8p325, Certificates.k16t8p325_check⟩

private theorem k16t8_cover690 : ∀ P ∈ pathPatterns 0 0 [1, 1, 1, 1, 1, 3], HasCheckedCertificate 16 8 ([[], [1, 1, 1, 1, 1, 3]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k16t8p326, Certificates.k16t8p326_check⟩

private theorem k16t8_cover691 : ∀ P ∈ pathPatterns 1 2 [1, 1, 1, 1, 2], HasCheckedCertificate 16 8 ([[], [1, 1, 1, 1, 2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [1, 1, 1, 1, 2] [] ∧ LexLE [] [])) h)

private theorem k16t8_cover692 : ∀ P ∈ pathPatterns 0 1 [1, 1, 1, 1, 2, 1], HasCheckedCertificate 16 8 ([[], [1, 1, 1, 1, 2, 1]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k16t8p327, Certificates.k16t8p327_check⟩

private theorem k16t8_cover693 : ∀ P ∈ pathPatterns 0 0 [1, 1, 1, 1, 2, 2], HasCheckedCertificate 16 8 ([[], [1, 1, 1, 1, 2, 2]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k16t8p328, Certificates.k16t8p328_check⟩

private theorem k16t8_cover694 : ∀ P ∈ pathPatterns 1 1 [1, 1, 1, 1, 3], HasCheckedCertificate 16 8 ([[], [1, 1, 1, 1, 3]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [1, 1, 1, 1, 3] [] ∧ LexLE [] [])) h)

private theorem k16t8_cover695 : ∀ P ∈ pathPatterns 0 0 [1, 1, 1, 1, 3, 1], HasCheckedCertificate 16 8 ([[], [1, 1, 1, 1, 3, 1]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k16t8p329, Certificates.k16t8p329_check⟩

private theorem k16t8_cover696 : ∀ P ∈ pathPatterns 1 0 [1, 1, 1, 1, 4], HasCheckedCertificate 16 8 ([[], [1, 1, 1, 1, 4]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [1, 1, 1, 1, 4] [] ∧ LexLE [] [])) h)

private theorem k16t8_cover698 : ∀ P ∈ pathPatterns 0 1 [2], HasCheckedCertificate 16 8 ([[], [1, 1, 1, 2], [2]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k16t8p330, Certificates.k16t8p330_check⟩

private theorem k16t8_cover699 : ∀ P ∈ pathPatterns 0 0 [3], HasCheckedCertificate 16 8 ([[], [1, 1, 1, 2], [3]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k16t8p331, Certificates.k16t8p331_check⟩

private theorem k16t8_cover697 : ∀ P ∈ pathPatterns 2 3 [1, 1, 1, 2], HasCheckedCertificate 16 8 ([[], [1, 1, 1, 2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [1, 1, 1, 2] [] ∧ LexLE [] [])) h)
      · intro q
        fin_cases q
        · exact by
            intro h
            exact False.elim ((by decide : ¬ (LexLE [1, 1, 1, 2] [1] ∧ LexLE [1] [1])) h)
        · exact by
            intro _
            exact k16t8_cover698
        · exact by
            intro _
            exact k16t8_cover699

private theorem k16t8_cover700 : ∀ P ∈ pathPatterns 1 2 [1, 1, 1, 2, 1], HasCheckedCertificate 16 8 ([[], [1, 1, 1, 2, 1]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [1, 1, 1, 2, 1] [] ∧ LexLE [] [])) h)

private theorem k16t8_cover701 : ∀ P ∈ pathPatterns 0 1 [1, 1, 1, 2, 1, 1], HasCheckedCertificate 16 8 ([[], [1, 1, 1, 2, 1, 1]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k16t8p332, Certificates.k16t8p332_check⟩

private theorem k16t8_cover702 : ∀ P ∈ pathPatterns 0 0 [1, 1, 1, 2, 1, 2], HasCheckedCertificate 16 8 ([[], [1, 1, 1, 2, 1, 2]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k16t8p333, Certificates.k16t8p333_check⟩

private theorem k16t8_cover703 : ∀ P ∈ pathPatterns 1 1 [1, 1, 1, 2, 2], HasCheckedCertificate 16 8 ([[], [1, 1, 1, 2, 2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [1, 1, 1, 2, 2] [] ∧ LexLE [] [])) h)

private theorem k16t8_cover704 : ∀ P ∈ pathPatterns 0 0 [1, 1, 1, 2, 2, 1], HasCheckedCertificate 16 8 ([[], [1, 1, 1, 2, 2, 1]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k16t8p334, Certificates.k16t8p334_check⟩

private theorem k16t8_cover705 : ∀ P ∈ pathPatterns 1 0 [1, 1, 1, 2, 3], HasCheckedCertificate 16 8 ([[], [1, 1, 1, 2, 3]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [1, 1, 1, 2, 3] [] ∧ LexLE [] [])) h)

private theorem k16t8_cover707 : ∀ P ∈ pathPatterns 0 0 [2], HasCheckedCertificate 16 8 ([[], [1, 1, 1, 3], [2]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k16t8p335, Certificates.k16t8p335_check⟩

private theorem k16t8_cover706 : ∀ P ∈ pathPatterns 2 2 [1, 1, 1, 3], HasCheckedCertificate 16 8 ([[], [1, 1, 1, 3]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [1, 1, 1, 3] [] ∧ LexLE [] [])) h)
      · intro q
        fin_cases q
        · exact by
            intro h
            exact False.elim ((by decide : ¬ (LexLE [1, 1, 1, 3] [1] ∧ LexLE [1] [1])) h)
        · exact by
            intro _
            exact k16t8_cover707

private theorem k16t8_cover708 : ∀ P ∈ pathPatterns 1 1 [1, 1, 1, 3, 1], HasCheckedCertificate 16 8 ([[], [1, 1, 1, 3, 1]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [1, 1, 1, 3, 1] [] ∧ LexLE [] [])) h)

private theorem k16t8_cover709 : ∀ P ∈ pathPatterns 0 0 [1, 1, 1, 3, 1, 1], HasCheckedCertificate 16 8 ([[], [1, 1, 1, 3, 1, 1]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k16t8p336, Certificates.k16t8p336_check⟩

private theorem k16t8_cover710 : ∀ P ∈ pathPatterns 1 0 [1, 1, 1, 3, 2], HasCheckedCertificate 16 8 ([[], [1, 1, 1, 3, 2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [1, 1, 1, 3, 2] [] ∧ LexLE [] [])) h)

private theorem k16t8_cover711 : ∀ P ∈ pathPatterns 2 1 [1, 1, 1, 4], HasCheckedCertificate 16 8 ([[], [1, 1, 1, 4]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [1, 1, 1, 4] [] ∧ LexLE [] [])) h)
      · intro q
        fin_cases q
        · exact by
            intro h
            exact False.elim ((by decide : ¬ (LexLE [1, 1, 1, 4] [1] ∧ LexLE [1] [1])) h)

private theorem k16t8_cover712 : ∀ P ∈ pathPatterns 1 0 [1, 1, 1, 4, 1], HasCheckedCertificate 16 8 ([[], [1, 1, 1, 4, 1]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [1, 1, 1, 4, 1] [] ∧ LexLE [] [])) h)

private theorem k16t8_cover713 : ∀ P ∈ pathPatterns 2 0 [1, 1, 1, 5], HasCheckedCertificate 16 8 ([[], [1, 1, 1, 5]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [1, 1, 1, 5] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k16t8_seq672 : amountSequenceForall 3 5 (fun tail =>
    (LexLE [] ([1, 1, 1] ++ tail) ∧ LexLE ([1, 1, 1] ++ tail) ([1, 1, 1] ++ tail).reverse) →
    ∀ P ∈ pathPatterns (6 - ([1, 1, 1] ++ tail).length) (8 - ([1, 1, 1] ++ tail).sum) ([1, 1, 1] ++ tail),
      HasCheckedCertificate 16 8 ([[]] ++ (([1, 1, 1] ++ tail) :: P))) :=
by
  constructor
  · exact by
      intro _
      exact k16t8_cover673
  · intro q
    fin_cases q
    · exact by
        constructor
        · exact by
            intro _
            exact k16t8_cover683
        · intro q
          fin_cases q
          · exact by
              constructor
              · exact by
                  intro _
                  exact k16t8_cover687
              · intro q
                fin_cases q
                · exact by
                    intro _
                    exact k16t8_cover688
                · exact by
                    intro _
                    exact k16t8_cover689
                · exact by
                    intro _
                    exact k16t8_cover690
          · exact by
              constructor
              · exact by
                  intro _
                  exact k16t8_cover691
              · intro q
                fin_cases q
                · exact by
                    intro _
                    exact k16t8_cover692
                · exact by
                    intro _
                    exact k16t8_cover693
          · exact by
              constructor
              · exact by
                  intro _
                  exact k16t8_cover694
              · intro q
                fin_cases q
                · exact by
                    intro _
                    exact k16t8_cover695
          · exact by
              constructor
              · exact by
                  intro _
                  exact k16t8_cover696
              · intro q
                exact Fin.elim0 q
    · exact by
        constructor
        · exact by
            intro _
            exact k16t8_cover697
        · intro q
          fin_cases q
          · exact by
              constructor
              · exact by
                  intro _
                  exact k16t8_cover700
              · intro q
                fin_cases q
                · exact by
                    intro _
                    exact k16t8_cover701
                · exact by
                    intro _
                    exact k16t8_cover702
          · exact by
              constructor
              · exact by
                  intro _
                  exact k16t8_cover703
              · intro q
                fin_cases q
                · exact by
                    intro _
                    exact k16t8_cover704
          · exact by
              constructor
              · exact by
                  intro _
                  exact k16t8_cover705
              · intro q
                exact Fin.elim0 q
    · exact by
        constructor
        · exact by
            intro _
            exact k16t8_cover706
        · intro q
          fin_cases q
          · exact by
              constructor
              · exact by
                  intro _
                  exact k16t8_cover708
              · intro q
                fin_cases q
                · exact by
                    intro _
                    exact k16t8_cover709
          · exact by
              constructor
              · exact by
                  intro _
                  exact k16t8_cover710
              · intro q
                exact Fin.elim0 q
    · exact by
        constructor
        · exact by
            intro _
            exact k16t8_cover711
        · intro q
          fin_cases q
          · exact by
              constructor
              · exact by
                  intro _
                  exact k16t8_cover712
              · intro q
                exact Fin.elim0 q
    · exact by
        constructor
        · exact by
            intro _
            exact k16t8_cover713
        · intro q
          exact Fin.elim0 q

private theorem k16t8_cover715 : ∀ P ∈ pathPatterns 0 1 [1, 2], HasCheckedCertificate 16 8 ([[], [1, 1, 2], [1, 2]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k16t8p337, Certificates.k16t8p337_check⟩

private theorem k16t8_cover716 : ∀ P ∈ pathPatterns 0 0 [1, 3], HasCheckedCertificate 16 8 ([[], [1, 1, 2], [1, 3]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k16t8p338, Certificates.k16t8p338_check⟩

private theorem k16t8_cover717 : ∀ P ∈ pathPatterns 1 2 [2], HasCheckedCertificate 16 8 ([[], [1, 1, 2], [2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [2] [] ∧ LexLE [] [])) h)

private theorem k16t8_cover718 : ∀ P ∈ pathPatterns 0 0 [2, 2], HasCheckedCertificate 16 8 ([[], [1, 1, 2], [2, 2]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k16t8p339, Certificates.k16t8p339_check⟩

private theorem k16t8_cover719 : ∀ P ∈ pathPatterns 1 1 [3], HasCheckedCertificate 16 8 ([[], [1, 1, 2], [3]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [3] [] ∧ LexLE [] [])) h)

private theorem k16t8_cover720 : ∀ P ∈ pathPatterns 1 0 [4], HasCheckedCertificate 16 8 ([[], [1, 1, 2], [4]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [4] [] ∧ LexLE [] [])) h)

private theorem k16t8_cover714 : ∀ P ∈ pathPatterns 3 4 [1, 1, 2], HasCheckedCertificate 16 8 ([[], [1, 1, 2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [1, 1, 2] [] ∧ LexLE [] [])) h)
      · intro q
        fin_cases q
        · exact by
            constructor
            · exact by
                intro h
                exact False.elim ((by decide : ¬ (LexLE [1, 1, 2] [1] ∧ LexLE [1] [1])) h)
            · intro q
              fin_cases q
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [1, 1, 2] [1, 1] ∧ LexLE [1, 1] [1, 1])) h)
              · exact by
                  intro _
                  exact k16t8_cover715
              · exact by
                  intro _
                  exact k16t8_cover716
        · exact by
            constructor
            · exact by
                intro _
                exact k16t8_cover717
            · intro q
              fin_cases q
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [1, 1, 2] [2, 1] ∧ LexLE [2, 1] [1, 2])) h)
              · exact by
                  intro _
                  exact k16t8_cover718
        · exact by
            constructor
            · exact by
                intro _
                exact k16t8_cover719
            · intro q
              fin_cases q
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [1, 1, 2] [3, 1] ∧ LexLE [3, 1] [1, 3])) h)
        · exact by
            constructor
            · exact by
                intro _
                exact k16t8_cover720
            · intro q
              exact Fin.elim0 q

private theorem k16t8_cover722 : ∀ P ∈ pathPatterns 0 1 [2], HasCheckedCertificate 16 8 ([[], [1, 1, 2, 1], [2]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k16t8p340, Certificates.k16t8p340_check⟩

private theorem k16t8_cover723 : ∀ P ∈ pathPatterns 0 0 [3], HasCheckedCertificate 16 8 ([[], [1, 1, 2, 1], [3]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k16t8p341, Certificates.k16t8p341_check⟩

private theorem k16t8_cover721 : ∀ P ∈ pathPatterns 2 3 [1, 1, 2, 1], HasCheckedCertificate 16 8 ([[], [1, 1, 2, 1]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [1, 1, 2, 1] [] ∧ LexLE [] [])) h)
      · intro q
        fin_cases q
        · exact by
            intro h
            exact False.elim ((by decide : ¬ (LexLE [1, 1, 2, 1] [1] ∧ LexLE [1] [1])) h)
        · exact by
            intro _
            exact k16t8_cover722
        · exact by
            intro _
            exact k16t8_cover723

private theorem k16t8_cover724 : ∀ P ∈ pathPatterns 1 2 [1, 1, 2, 1, 1], HasCheckedCertificate 16 8 ([[], [1, 1, 2, 1, 1]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [1, 1, 2, 1, 1] [] ∧ LexLE [] [])) h)

private theorem k16t8_cover725 : ∀ P ∈ pathPatterns 0 0 [1, 1, 2, 1, 1, 2], HasCheckedCertificate 16 8 ([[], [1, 1, 2, 1, 1, 2]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k16t8p342, Certificates.k16t8p342_check⟩

private theorem k16t8_cover726 : ∀ P ∈ pathPatterns 1 1 [1, 1, 2, 1, 2], HasCheckedCertificate 16 8 ([[], [1, 1, 2, 1, 2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [1, 1, 2, 1, 2] [] ∧ LexLE [] [])) h)

private theorem k16t8_cover727 : ∀ P ∈ pathPatterns 0 0 [1, 1, 2, 1, 2, 1], HasCheckedCertificate 16 8 ([[], [1, 1, 2, 1, 2, 1]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k16t8p343, Certificates.k16t8p343_check⟩

private theorem k16t8_cover728 : ∀ P ∈ pathPatterns 1 0 [1, 1, 2, 1, 3], HasCheckedCertificate 16 8 ([[], [1, 1, 2, 1, 3]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [1, 1, 2, 1, 3] [] ∧ LexLE [] [])) h)

private theorem k16t8_cover730 : ∀ P ∈ pathPatterns 0 0 [2], HasCheckedCertificate 16 8 ([[], [1, 1, 2, 2], [2]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k16t8p344, Certificates.k16t8p344_check⟩

private theorem k16t8_cover729 : ∀ P ∈ pathPatterns 2 2 [1, 1, 2, 2], HasCheckedCertificate 16 8 ([[], [1, 1, 2, 2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [1, 1, 2, 2] [] ∧ LexLE [] [])) h)
      · intro q
        fin_cases q
        · exact by
            intro h
            exact False.elim ((by decide : ¬ (LexLE [1, 1, 2, 2] [1] ∧ LexLE [1] [1])) h)
        · exact by
            intro _
            exact k16t8_cover730

private theorem k16t8_cover731 : ∀ P ∈ pathPatterns 1 1 [1, 1, 2, 2, 1], HasCheckedCertificate 16 8 ([[], [1, 1, 2, 2, 1]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [1, 1, 2, 2, 1] [] ∧ LexLE [] [])) h)

private theorem k16t8_cover732 : ∀ P ∈ pathPatterns 0 0 [1, 1, 2, 2, 1, 1], HasCheckedCertificate 16 8 ([[], [1, 1, 2, 2, 1, 1]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k16t8p345, Certificates.k16t8p345_check⟩

private theorem k16t8_cover733 : ∀ P ∈ pathPatterns 1 0 [1, 1, 2, 2, 2], HasCheckedCertificate 16 8 ([[], [1, 1, 2, 2, 2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [1, 1, 2, 2, 2] [] ∧ LexLE [] [])) h)

private theorem k16t8_cover734 : ∀ P ∈ pathPatterns 2 1 [1, 1, 2, 3], HasCheckedCertificate 16 8 ([[], [1, 1, 2, 3]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [1, 1, 2, 3] [] ∧ LexLE [] [])) h)
      · intro q
        fin_cases q
        · exact by
            intro h
            exact False.elim ((by decide : ¬ (LexLE [1, 1, 2, 3] [1] ∧ LexLE [1] [1])) h)

private theorem k16t8_cover735 : ∀ P ∈ pathPatterns 1 0 [1, 1, 2, 3, 1], HasCheckedCertificate 16 8 ([[], [1, 1, 2, 3, 1]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [1, 1, 2, 3, 1] [] ∧ LexLE [] [])) h)

private theorem k16t8_cover736 : ∀ P ∈ pathPatterns 2 0 [1, 1, 2, 4], HasCheckedCertificate 16 8 ([[], [1, 1, 2, 4]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [1, 1, 2, 4] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k16t8_cover738 : ∀ P ∈ pathPatterns 0 0 [1, 2], HasCheckedCertificate 16 8 ([[], [1, 1, 3], [1, 2]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k16t8p346, Certificates.k16t8p346_check⟩

private theorem k16t8_cover739 : ∀ P ∈ pathPatterns 1 1 [2], HasCheckedCertificate 16 8 ([[], [1, 1, 3], [2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [2] [] ∧ LexLE [] [])) h)

private theorem k16t8_cover740 : ∀ P ∈ pathPatterns 1 0 [3], HasCheckedCertificate 16 8 ([[], [1, 1, 3], [3]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [3] [] ∧ LexLE [] [])) h)

private theorem k16t8_cover737 : ∀ P ∈ pathPatterns 3 3 [1, 1, 3], HasCheckedCertificate 16 8 ([[], [1, 1, 3]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [1, 1, 3] [] ∧ LexLE [] [])) h)
      · intro q
        fin_cases q
        · exact by
            constructor
            · exact by
                intro h
                exact False.elim ((by decide : ¬ (LexLE [1, 1, 3] [1] ∧ LexLE [1] [1])) h)
            · intro q
              fin_cases q
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [1, 1, 3] [1, 1] ∧ LexLE [1, 1] [1, 1])) h)
              · exact by
                  intro _
                  exact k16t8_cover738
        · exact by
            constructor
            · exact by
                intro _
                exact k16t8_cover739
            · intro q
              fin_cases q
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [1, 1, 3] [2, 1] ∧ LexLE [2, 1] [1, 2])) h)
        · exact by
            constructor
            · exact by
                intro _
                exact k16t8_cover740
            · intro q
              exact Fin.elim0 q

private theorem k16t8_cover742 : ∀ P ∈ pathPatterns 0 0 [2], HasCheckedCertificate 16 8 ([[], [1, 1, 3, 1], [2]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k16t8p347, Certificates.k16t8p347_check⟩

private theorem k16t8_cover741 : ∀ P ∈ pathPatterns 2 2 [1, 1, 3, 1], HasCheckedCertificate 16 8 ([[], [1, 1, 3, 1]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [1, 1, 3, 1] [] ∧ LexLE [] [])) h)
      · intro q
        fin_cases q
        · exact by
            intro h
            exact False.elim ((by decide : ¬ (LexLE [1, 1, 3, 1] [1] ∧ LexLE [1] [1])) h)
        · exact by
            intro _
            exact k16t8_cover742

private theorem k16t8_cover743 : ∀ P ∈ pathPatterns 1 1 [1, 1, 3, 1, 1], HasCheckedCertificate 16 8 ([[], [1, 1, 3, 1, 1]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [1, 1, 3, 1, 1] [] ∧ LexLE [] [])) h)

private theorem k16t8_cover744 : ∀ P ∈ pathPatterns 1 0 [1, 1, 3, 1, 2], HasCheckedCertificate 16 8 ([[], [1, 1, 3, 1, 2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [1, 1, 3, 1, 2] [] ∧ LexLE [] [])) h)

private theorem k16t8_cover745 : ∀ P ∈ pathPatterns 2 1 [1, 1, 3, 2], HasCheckedCertificate 16 8 ([[], [1, 1, 3, 2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [1, 1, 3, 2] [] ∧ LexLE [] [])) h)
      · intro q
        fin_cases q
        · exact by
            intro h
            exact False.elim ((by decide : ¬ (LexLE [1, 1, 3, 2] [1] ∧ LexLE [1] [1])) h)

private theorem k16t8_cover746 : ∀ P ∈ pathPatterns 1 0 [1, 1, 3, 2, 1], HasCheckedCertificate 16 8 ([[], [1, 1, 3, 2, 1]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [1, 1, 3, 2, 1] [] ∧ LexLE [] [])) h)

private theorem k16t8_cover747 : ∀ P ∈ pathPatterns 2 0 [1, 1, 3, 3], HasCheckedCertificate 16 8 ([[], [1, 1, 3, 3]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [1, 1, 3, 3] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k16t8_cover749 : ∀ P ∈ pathPatterns 1 0 [2], HasCheckedCertificate 16 8 ([[], [1, 1, 4], [2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [2] [] ∧ LexLE [] [])) h)

private theorem k16t8_cover748 : ∀ P ∈ pathPatterns 3 2 [1, 1, 4], HasCheckedCertificate 16 8 ([[], [1, 1, 4]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [1, 1, 4] [] ∧ LexLE [] [])) h)
      · intro q
        fin_cases q
        · exact by
            constructor
            · exact by
                intro h
                exact False.elim ((by decide : ¬ (LexLE [1, 1, 4] [1] ∧ LexLE [1] [1])) h)
            · intro q
              fin_cases q
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [1, 1, 4] [1, 1] ∧ LexLE [1, 1] [1, 1])) h)
        · exact by
            constructor
            · exact by
                intro _
                exact k16t8_cover749
            · intro q
              exact Fin.elim0 q

private theorem k16t8_cover750 : ∀ P ∈ pathPatterns 2 1 [1, 1, 4, 1], HasCheckedCertificate 16 8 ([[], [1, 1, 4, 1]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [1, 1, 4, 1] [] ∧ LexLE [] [])) h)
      · intro q
        fin_cases q
        · exact by
            intro h
            exact False.elim ((by decide : ¬ (LexLE [1, 1, 4, 1] [1] ∧ LexLE [1] [1])) h)

private theorem k16t8_cover751 : ∀ P ∈ pathPatterns 1 0 [1, 1, 4, 1, 1], HasCheckedCertificate 16 8 ([[], [1, 1, 4, 1, 1]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [1, 1, 4, 1, 1] [] ∧ LexLE [] [])) h)

private theorem k16t8_cover752 : ∀ P ∈ pathPatterns 2 0 [1, 1, 4, 2], HasCheckedCertificate 16 8 ([[], [1, 1, 4, 2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [1, 1, 4, 2] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k16t8_cover753 : ∀ P ∈ pathPatterns 3 1 [1, 1, 5], HasCheckedCertificate 16 8 ([[], [1, 1, 5]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [1, 1, 5] [] ∧ LexLE [] [])) h)
      · intro q
        fin_cases q
        · exact by
            constructor
            · exact by
                intro h
                exact False.elim ((by decide : ¬ (LexLE [1, 1, 5] [1] ∧ LexLE [1] [1])) h)
            · intro q
              exact Fin.elim0 q

private theorem k16t8_cover754 : ∀ P ∈ pathPatterns 2 0 [1, 1, 5, 1], HasCheckedCertificate 16 8 ([[], [1, 1, 5, 1]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [1, 1, 5, 1] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k16t8_cover755 : ∀ P ∈ pathPatterns 3 0 [1, 1, 6], HasCheckedCertificate 16 8 ([[], [1, 1, 6]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [1, 1, 6] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k16t8_seq638 : amountSequenceForall 4 6 (fun tail =>
    (LexLE [] ([1, 1] ++ tail) ∧ LexLE ([1, 1] ++ tail) ([1, 1] ++ tail).reverse) →
    ∀ P ∈ pathPatterns (6 - ([1, 1] ++ tail).length) (8 - ([1, 1] ++ tail).sum) ([1, 1] ++ tail),
      HasCheckedCertificate 16 8 ([[]] ++ (([1, 1] ++ tail) :: P))) :=
by
  constructor
  · exact by
      intro _
      exact k16t8_cover639
  · intro q
    fin_cases q
    · exact k16t8_seq672

    · exact by
        constructor
        · exact by
            intro _
            exact k16t8_cover714
        · intro q
          fin_cases q
          · exact by
              constructor
              · exact by
                  intro _
                  exact k16t8_cover721
              · intro q
                fin_cases q
                · exact by
                    constructor
                    · exact by
                        intro _
                        exact k16t8_cover724
                    · intro q
                      fin_cases q
                      · exact by
                          intro h
                          exact False.elim ((by decide : ¬ (LexLE [] [1, 1, 2, 1, 1, 1] ∧ LexLE [1, 1, 2, 1, 1, 1] [1, 1, 1, 2, 1, 1])) h)
                      · exact by
                          intro _
                          exact k16t8_cover725
                · exact by
                    constructor
                    · exact by
                        intro _
                        exact k16t8_cover726
                    · intro q
                      fin_cases q
                      · exact by
                          intro _
                          exact k16t8_cover727
                · exact by
                    constructor
                    · exact by
                        intro _
                        exact k16t8_cover728
                    · intro q
                      exact Fin.elim0 q
          · exact by
              constructor
              · exact by
                  intro _
                  exact k16t8_cover729
              · intro q
                fin_cases q
                · exact by
                    constructor
                    · exact by
                        intro _
                        exact k16t8_cover731
                    · intro q
                      fin_cases q
                      · exact by
                          intro _
                          exact k16t8_cover732
                · exact by
                    constructor
                    · exact by
                        intro _
                        exact k16t8_cover733
                    · intro q
                      exact Fin.elim0 q
          · exact by
              constructor
              · exact by
                  intro _
                  exact k16t8_cover734
              · intro q
                fin_cases q
                · exact by
                    constructor
                    · exact by
                        intro _
                        exact k16t8_cover735
                    · intro q
                      exact Fin.elim0 q
          · exact by
              constructor
              · exact by
                  intro _
                  exact k16t8_cover736
              · intro q
                exact Fin.elim0 q
    · exact by
        constructor
        · exact by
            intro _
            exact k16t8_cover737
        · intro q
          fin_cases q
          · exact by
              constructor
              · exact by
                  intro _
                  exact k16t8_cover741
              · intro q
                fin_cases q
                · exact by
                    constructor
                    · exact by
                        intro _
                        exact k16t8_cover743
                    · intro q
                      fin_cases q
                      · exact by
                          intro h
                          exact False.elim ((by decide : ¬ (LexLE [] [1, 1, 3, 1, 1, 1] ∧ LexLE [1, 1, 3, 1, 1, 1] [1, 1, 1, 3, 1, 1])) h)
                · exact by
                    constructor
                    · exact by
                        intro _
                        exact k16t8_cover744
                    · intro q
                      exact Fin.elim0 q
          · exact by
              constructor
              · exact by
                  intro _
                  exact k16t8_cover745
              · intro q
                fin_cases q
                · exact by
                    constructor
                    · exact by
                        intro _
                        exact k16t8_cover746
                    · intro q
                      exact Fin.elim0 q
          · exact by
              constructor
              · exact by
                  intro _
                  exact k16t8_cover747
              · intro q
                exact Fin.elim0 q
    · exact by
        constructor
        · exact by
            intro _
            exact k16t8_cover748
        · intro q
          fin_cases q
          · exact by
              constructor
              · exact by
                  intro _
                  exact k16t8_cover750
              · intro q
                fin_cases q
                · exact by
                    constructor
                    · exact by
                        intro _
                        exact k16t8_cover751
                    · intro q
                      exact Fin.elim0 q
          · exact by
              constructor
              · exact by
                  intro _
                  exact k16t8_cover752
              · intro q
                exact Fin.elim0 q
    · exact by
        constructor
        · exact by
            intro _
            exact k16t8_cover753
        · intro q
          fin_cases q
          · exact by
              constructor
              · exact by
                  intro _
                  exact k16t8_cover754
              · intro q
                exact Fin.elim0 q
    · exact by
        constructor
        · exact by
            intro _
            exact k16t8_cover755
        · intro q
          exact Fin.elim0 q

private theorem k16t8_cover759 : ∀ P ∈ pathPatterns 1 2 [1, 2], HasCheckedCertificate 16 8 ([[], [1, 2], [1, 2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [1, 2] [] ∧ LexLE [] [])) h)

private theorem k16t8_cover760 : ∀ P ∈ pathPatterns 0 1 [1, 2, 1], HasCheckedCertificate 16 8 ([[], [1, 2], [1, 2, 1]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k16t8p348, Certificates.k16t8p348_check⟩

private theorem k16t8_cover761 : ∀ P ∈ pathPatterns 0 0 [1, 2, 2], HasCheckedCertificate 16 8 ([[], [1, 2], [1, 2, 2]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k16t8p349, Certificates.k16t8p349_check⟩

private theorem k16t8_cover762 : ∀ P ∈ pathPatterns 1 1 [1, 3], HasCheckedCertificate 16 8 ([[], [1, 2], [1, 3]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [1, 3] [] ∧ LexLE [] [])) h)

private theorem k16t8_cover763 : ∀ P ∈ pathPatterns 0 0 [1, 3, 1], HasCheckedCertificate 16 8 ([[], [1, 2], [1, 3, 1]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k16t8p350, Certificates.k16t8p350_check⟩

private theorem k16t8_cover764 : ∀ P ∈ pathPatterns 1 0 [1, 4], HasCheckedCertificate 16 8 ([[], [1, 2], [1, 4]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [1, 4] [] ∧ LexLE [] [])) h)

private theorem k16t8_cover766 : ∀ P ∈ pathPatterns 0 1 [2], HasCheckedCertificate 16 8 ([[], [1, 2], [2], [2]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k16t8p351, Certificates.k16t8p351_check⟩

private theorem k16t8_cover767 : ∀ P ∈ pathPatterns 0 0 [3], HasCheckedCertificate 16 8 ([[], [1, 2], [2], [3]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k16t8p352, Certificates.k16t8p352_check⟩

private theorem k16t8_cover765 : ∀ P ∈ pathPatterns 2 3 [2], HasCheckedCertificate 16 8 ([[], [1, 2], [2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [2] [] ∧ LexLE [] [])) h)
      · intro q
        fin_cases q
        · exact by
            intro h
            exact False.elim ((by decide : ¬ (LexLE [2] [1] ∧ LexLE [1] [1])) h)
        · exact by
            intro _
            exact k16t8_cover766
        · exact by
            intro _
            exact k16t8_cover767

private theorem k16t8_cover768 : ∀ P ∈ pathPatterns 0 0 [2, 1, 2], HasCheckedCertificate 16 8 ([[], [1, 2], [2, 1, 2]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k16t8p353, Certificates.k16t8p353_check⟩

private theorem k16t8_cover769 : ∀ P ∈ pathPatterns 1 1 [2, 2], HasCheckedCertificate 16 8 ([[], [1, 2], [2, 2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [2, 2] [] ∧ LexLE [] [])) h)

private theorem k16t8_cover770 : ∀ P ∈ pathPatterns 1 0 [2, 3], HasCheckedCertificate 16 8 ([[], [1, 2], [2, 3]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [2, 3] [] ∧ LexLE [] [])) h)

private theorem k16t8_cover771 : ∀ P ∈ pathPatterns 2 2 [3], HasCheckedCertificate 16 8 ([[], [1, 2], [3]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [3] [] ∧ LexLE [] [])) h)
      · intro q
        fin_cases q
        · exact by
            intro h
            exact False.elim ((by decide : ¬ (LexLE [3] [1] ∧ LexLE [1] [1])) h)
        · exact by
            intro h
            exact False.elim ((by decide : ¬ (LexLE [3] [2] ∧ LexLE [2] [2])) h)

private theorem k16t8_cover772 : ∀ P ∈ pathPatterns 2 1 [4], HasCheckedCertificate 16 8 ([[], [1, 2], [4]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [4] [] ∧ LexLE [] [])) h)
      · intro q
        fin_cases q
        · exact by
            intro h
            exact False.elim ((by decide : ¬ (LexLE [4] [1] ∧ LexLE [1] [1])) h)

private theorem k16t8_cover773 : ∀ P ∈ pathPatterns 2 0 [5], HasCheckedCertificate 16 8 ([[], [1, 2], [5]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [5] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k16t8_seq758 : amountSequenceForall 3 5 (fun tail =>
    (LexLE [1, 2] ([] ++ tail) ∧ LexLE ([] ++ tail) ([] ++ tail).reverse) →
    ∀ P ∈ pathPatterns (3 - ([] ++ tail).length) (5 - ([] ++ tail).sum) ([] ++ tail),
      HasCheckedCertificate 16 8 ([[], [1, 2]] ++ (([] ++ tail) :: P))) :=
by
  constructor
  · exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [1, 2] [] ∧ LexLE [] [])) h)
  · intro q
    fin_cases q
    · exact by
        constructor
        · exact by
            intro h
            exact False.elim ((by decide : ¬ (LexLE [1, 2] [1] ∧ LexLE [1] [1])) h)
        · intro q
          fin_cases q
          · exact by
              constructor
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [1, 2] [1, 1] ∧ LexLE [1, 1] [1, 1])) h)
              · intro q
                fin_cases q
                · exact by
                    intro h
                    exact False.elim ((by decide : ¬ (LexLE [1, 2] [1, 1, 1] ∧ LexLE [1, 1, 1] [1, 1, 1])) h)
                · exact by
                    intro h
                    exact False.elim ((by decide : ¬ (LexLE [1, 2] [1, 1, 2] ∧ LexLE [1, 1, 2] [2, 1, 1])) h)
                · exact by
                    intro h
                    exact False.elim ((by decide : ¬ (LexLE [1, 2] [1, 1, 3] ∧ LexLE [1, 1, 3] [3, 1, 1])) h)
          · exact by
              constructor
              · exact by
                  intro _
                  exact k16t8_cover759
              · intro q
                fin_cases q
                · exact by
                    intro _
                    exact k16t8_cover760
                · exact by
                    intro _
                    exact k16t8_cover761
          · exact by
              constructor
              · exact by
                  intro _
                  exact k16t8_cover762
              · intro q
                fin_cases q
                · exact by
                    intro _
                    exact k16t8_cover763
          · exact by
              constructor
              · exact by
                  intro _
                  exact k16t8_cover764
              · intro q
                exact Fin.elim0 q
    · exact by
        constructor
        · exact by
            intro _
            exact k16t8_cover765
        · intro q
          fin_cases q
          · exact by
              constructor
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [1, 2] [2, 1] ∧ LexLE [2, 1] [1, 2])) h)
              · intro q
                fin_cases q
                · exact by
                    intro h
                    exact False.elim ((by decide : ¬ (LexLE [1, 2] [2, 1, 1] ∧ LexLE [2, 1, 1] [1, 1, 2])) h)
                · exact by
                    intro _
                    exact k16t8_cover768
          · exact by
              constructor
              · exact by
                  intro _
                  exact k16t8_cover769
              · intro q
                fin_cases q
                · exact by
                    intro h
                    exact False.elim ((by decide : ¬ (LexLE [1, 2] [2, 2, 1] ∧ LexLE [2, 2, 1] [1, 2, 2])) h)
          · exact by
              constructor
              · exact by
                  intro _
                  exact k16t8_cover770
              · intro q
                exact Fin.elim0 q
    · exact by
        constructor
        · exact by
            intro _
            exact k16t8_cover771
        · intro q
          fin_cases q
          · exact by
              constructor
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [1, 2] [3, 1] ∧ LexLE [3, 1] [1, 3])) h)
              · intro q
                fin_cases q
                · exact by
                    intro h
                    exact False.elim ((by decide : ¬ (LexLE [1, 2] [3, 1, 1] ∧ LexLE [3, 1, 1] [1, 1, 3])) h)
          · exact by
              constructor
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [1, 2] [3, 2] ∧ LexLE [3, 2] [2, 3])) h)
              · intro q
                exact Fin.elim0 q
    · exact by
        constructor
        · exact by
            intro _
            exact k16t8_cover772
        · intro q
          fin_cases q
          · exact by
              constructor
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [1, 2] [4, 1] ∧ LexLE [4, 1] [1, 4])) h)
              · intro q
                exact Fin.elim0 q
    · exact by
        constructor
        · exact by
            intro _
            exact k16t8_cover773
        · intro q
          exact Fin.elim0 q

private theorem k16t8_cover757 : ∀ P ∈ pathPatterns 4 5 [1, 2], HasCheckedCertificate 16 8 ([[], [1, 2]] ++ P) := by
  apply pathPatterns_forall_step
  exact k16t8_seq758


private theorem k16t8_cover775 : ∀ P ∈ pathPatterns 0 0 [1, 3], HasCheckedCertificate 16 8 ([[], [1, 2, 1], [1, 3]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k16t8p354, Certificates.k16t8p354_check⟩

private theorem k16t8_cover776 : ∀ P ∈ pathPatterns 1 2 [2], HasCheckedCertificate 16 8 ([[], [1, 2, 1], [2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [2] [] ∧ LexLE [] [])) h)

private theorem k16t8_cover777 : ∀ P ∈ pathPatterns 0 0 [2, 2], HasCheckedCertificate 16 8 ([[], [1, 2, 1], [2, 2]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k16t8p355, Certificates.k16t8p355_check⟩

private theorem k16t8_cover778 : ∀ P ∈ pathPatterns 1 1 [3], HasCheckedCertificate 16 8 ([[], [1, 2, 1], [3]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [3] [] ∧ LexLE [] [])) h)

private theorem k16t8_cover779 : ∀ P ∈ pathPatterns 1 0 [4], HasCheckedCertificate 16 8 ([[], [1, 2, 1], [4]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [4] [] ∧ LexLE [] [])) h)

private theorem k16t8_cover774 : ∀ P ∈ pathPatterns 3 4 [1, 2, 1], HasCheckedCertificate 16 8 ([[], [1, 2, 1]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [1, 2, 1] [] ∧ LexLE [] [])) h)
      · intro q
        fin_cases q
        · exact by
            constructor
            · exact by
                intro h
                exact False.elim ((by decide : ¬ (LexLE [1, 2, 1] [1] ∧ LexLE [1] [1])) h)
            · intro q
              fin_cases q
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [1, 2, 1] [1, 1] ∧ LexLE [1, 1] [1, 1])) h)
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [1, 2, 1] [1, 2] ∧ LexLE [1, 2] [2, 1])) h)
              · exact by
                  intro _
                  exact k16t8_cover775
        · exact by
            constructor
            · exact by
                intro _
                exact k16t8_cover776
            · intro q
              fin_cases q
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [1, 2, 1] [2, 1] ∧ LexLE [2, 1] [1, 2])) h)
              · exact by
                  intro _
                  exact k16t8_cover777
        · exact by
            constructor
            · exact by
                intro _
                exact k16t8_cover778
            · intro q
              fin_cases q
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [1, 2, 1] [3, 1] ∧ LexLE [3, 1] [1, 3])) h)
        · exact by
            constructor
            · exact by
                intro _
                exact k16t8_cover779
            · intro q
              exact Fin.elim0 q

private theorem k16t8_cover780 : ∀ P ∈ pathPatterns 0 0 [1, 2, 1, 1, 1, 2], HasCheckedCertificate 16 8 ([[], [1, 2, 1, 1, 1, 2]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k16t8p356, Certificates.k16t8p356_check⟩

private theorem k16t8_cover781 : ∀ P ∈ pathPatterns 1 1 [1, 2, 1, 1, 2], HasCheckedCertificate 16 8 ([[], [1, 2, 1, 1, 2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [1, 2, 1, 1, 2] [] ∧ LexLE [] [])) h)

private theorem k16t8_cover782 : ∀ P ∈ pathPatterns 0 0 [1, 2, 1, 1, 2, 1], HasCheckedCertificate 16 8 ([[], [1, 2, 1, 1, 2, 1]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k16t8p357, Certificates.k16t8p357_check⟩

private theorem k16t8_cover783 : ∀ P ∈ pathPatterns 1 0 [1, 2, 1, 1, 3], HasCheckedCertificate 16 8 ([[], [1, 2, 1, 1, 3]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [1, 2, 1, 1, 3] [] ∧ LexLE [] [])) h)

private theorem k16t8_cover785 : ∀ P ∈ pathPatterns 0 0 [2], HasCheckedCertificate 16 8 ([[], [1, 2, 1, 2], [2]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k16t8p358, Certificates.k16t8p358_check⟩

private theorem k16t8_cover784 : ∀ P ∈ pathPatterns 2 2 [1, 2, 1, 2], HasCheckedCertificate 16 8 ([[], [1, 2, 1, 2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [1, 2, 1, 2] [] ∧ LexLE [] [])) h)
      · intro q
        fin_cases q
        · exact by
            intro h
            exact False.elim ((by decide : ¬ (LexLE [1, 2, 1, 2] [1] ∧ LexLE [1] [1])) h)
        · exact by
            intro _
            exact k16t8_cover785

private theorem k16t8_cover786 : ∀ P ∈ pathPatterns 1 1 [1, 2, 1, 2, 1], HasCheckedCertificate 16 8 ([[], [1, 2, 1, 2, 1]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [1, 2, 1, 2, 1] [] ∧ LexLE [] [])) h)

private theorem k16t8_cover787 : ∀ P ∈ pathPatterns 1 0 [1, 2, 1, 2, 2], HasCheckedCertificate 16 8 ([[], [1, 2, 1, 2, 2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [1, 2, 1, 2, 2] [] ∧ LexLE [] [])) h)

private theorem k16t8_cover788 : ∀ P ∈ pathPatterns 2 1 [1, 2, 1, 3], HasCheckedCertificate 16 8 ([[], [1, 2, 1, 3]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [1, 2, 1, 3] [] ∧ LexLE [] [])) h)
      · intro q
        fin_cases q
        · exact by
            intro h
            exact False.elim ((by decide : ¬ (LexLE [1, 2, 1, 3] [1] ∧ LexLE [1] [1])) h)

private theorem k16t8_cover789 : ∀ P ∈ pathPatterns 1 0 [1, 2, 1, 3, 1], HasCheckedCertificate 16 8 ([[], [1, 2, 1, 3, 1]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [1, 2, 1, 3, 1] [] ∧ LexLE [] [])) h)

private theorem k16t8_cover790 : ∀ P ∈ pathPatterns 2 0 [1, 2, 1, 4], HasCheckedCertificate 16 8 ([[], [1, 2, 1, 4]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [1, 2, 1, 4] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k16t8_cover792 : ∀ P ∈ pathPatterns 1 1 [2], HasCheckedCertificate 16 8 ([[], [1, 2, 2], [2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [2] [] ∧ LexLE [] [])) h)

private theorem k16t8_cover793 : ∀ P ∈ pathPatterns 1 0 [3], HasCheckedCertificate 16 8 ([[], [1, 2, 2], [3]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [3] [] ∧ LexLE [] [])) h)

private theorem k16t8_cover791 : ∀ P ∈ pathPatterns 3 3 [1, 2, 2], HasCheckedCertificate 16 8 ([[], [1, 2, 2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [1, 2, 2] [] ∧ LexLE [] [])) h)
      · intro q
        fin_cases q
        · exact by
            constructor
            · exact by
                intro h
                exact False.elim ((by decide : ¬ (LexLE [1, 2, 2] [1] ∧ LexLE [1] [1])) h)
            · intro q
              fin_cases q
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [1, 2, 2] [1, 1] ∧ LexLE [1, 1] [1, 1])) h)
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [1, 2, 2] [1, 2] ∧ LexLE [1, 2] [2, 1])) h)
        · exact by
            constructor
            · exact by
                intro _
                exact k16t8_cover792
            · intro q
              fin_cases q
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [1, 2, 2] [2, 1] ∧ LexLE [2, 1] [1, 2])) h)
        · exact by
            constructor
            · exact by
                intro _
                exact k16t8_cover793
            · intro q
              exact Fin.elim0 q

private theorem k16t8_cover795 : ∀ P ∈ pathPatterns 0 0 [2], HasCheckedCertificate 16 8 ([[], [1, 2, 2, 1], [2]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k16t8p359, Certificates.k16t8p359_check⟩

private theorem k16t8_cover794 : ∀ P ∈ pathPatterns 2 2 [1, 2, 2, 1], HasCheckedCertificate 16 8 ([[], [1, 2, 2, 1]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [1, 2, 2, 1] [] ∧ LexLE [] [])) h)
      · intro q
        fin_cases q
        · exact by
            intro h
            exact False.elim ((by decide : ¬ (LexLE [1, 2, 2, 1] [1] ∧ LexLE [1] [1])) h)
        · exact by
            intro _
            exact k16t8_cover795

private theorem k16t8_cover796 : ∀ P ∈ pathPatterns 1 0 [1, 2, 2, 1, 2], HasCheckedCertificate 16 8 ([[], [1, 2, 2, 1, 2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [1, 2, 2, 1, 2] [] ∧ LexLE [] [])) h)

private theorem k16t8_cover797 : ∀ P ∈ pathPatterns 2 1 [1, 2, 2, 2], HasCheckedCertificate 16 8 ([[], [1, 2, 2, 2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [1, 2, 2, 2] [] ∧ LexLE [] [])) h)
      · intro q
        fin_cases q
        · exact by
            intro h
            exact False.elim ((by decide : ¬ (LexLE [1, 2, 2, 2] [1] ∧ LexLE [1] [1])) h)

private theorem k16t8_cover798 : ∀ P ∈ pathPatterns 1 0 [1, 2, 2, 2, 1], HasCheckedCertificate 16 8 ([[], [1, 2, 2, 2, 1]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [1, 2, 2, 2, 1] [] ∧ LexLE [] [])) h)

private theorem k16t8_cover799 : ∀ P ∈ pathPatterns 2 0 [1, 2, 2, 3], HasCheckedCertificate 16 8 ([[], [1, 2, 2, 3]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [1, 2, 2, 3] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k16t8_cover801 : ∀ P ∈ pathPatterns 1 0 [2], HasCheckedCertificate 16 8 ([[], [1, 2, 3], [2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [2] [] ∧ LexLE [] [])) h)

private theorem k16t8_cover800 : ∀ P ∈ pathPatterns 3 2 [1, 2, 3], HasCheckedCertificate 16 8 ([[], [1, 2, 3]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [1, 2, 3] [] ∧ LexLE [] [])) h)
      · intro q
        fin_cases q
        · exact by
            constructor
            · exact by
                intro h
                exact False.elim ((by decide : ¬ (LexLE [1, 2, 3] [1] ∧ LexLE [1] [1])) h)
            · intro q
              fin_cases q
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [1, 2, 3] [1, 1] ∧ LexLE [1, 1] [1, 1])) h)
        · exact by
            constructor
            · exact by
                intro _
                exact k16t8_cover801
            · intro q
              exact Fin.elim0 q

private theorem k16t8_cover802 : ∀ P ∈ pathPatterns 2 1 [1, 2, 3, 1], HasCheckedCertificate 16 8 ([[], [1, 2, 3, 1]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [1, 2, 3, 1] [] ∧ LexLE [] [])) h)
      · intro q
        fin_cases q
        · exact by
            intro h
            exact False.elim ((by decide : ¬ (LexLE [1, 2, 3, 1] [1] ∧ LexLE [1] [1])) h)

private theorem k16t8_cover803 : ∀ P ∈ pathPatterns 2 0 [1, 2, 3, 2], HasCheckedCertificate 16 8 ([[], [1, 2, 3, 2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [1, 2, 3, 2] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k16t8_cover804 : ∀ P ∈ pathPatterns 3 1 [1, 2, 4], HasCheckedCertificate 16 8 ([[], [1, 2, 4]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [1, 2, 4] [] ∧ LexLE [] [])) h)
      · intro q
        fin_cases q
        · exact by
            constructor
            · exact by
                intro h
                exact False.elim ((by decide : ¬ (LexLE [1, 2, 4] [1] ∧ LexLE [1] [1])) h)
            · intro q
              exact Fin.elim0 q

private theorem k16t8_cover805 : ∀ P ∈ pathPatterns 2 0 [1, 2, 4, 1], HasCheckedCertificate 16 8 ([[], [1, 2, 4, 1]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [1, 2, 4, 1] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k16t8_cover806 : ∀ P ∈ pathPatterns 3 0 [1, 2, 5], HasCheckedCertificate 16 8 ([[], [1, 2, 5]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [1, 2, 5] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k16t8_seq756 : amountSequenceForall 4 5 (fun tail =>
    (LexLE [] ([1, 2] ++ tail) ∧ LexLE ([1, 2] ++ tail) ([1, 2] ++ tail).reverse) →
    ∀ P ∈ pathPatterns (6 - ([1, 2] ++ tail).length) (8 - ([1, 2] ++ tail).sum) ([1, 2] ++ tail),
      HasCheckedCertificate 16 8 ([[]] ++ (([1, 2] ++ tail) :: P))) :=
by
  constructor
  · exact by
      intro _
      exact k16t8_cover757
  · intro q
    fin_cases q
    · exact by
        constructor
        · exact by
            intro _
            exact k16t8_cover774
        · intro q
          fin_cases q
          · exact by
              constructor
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [] [1, 2, 1, 1] ∧ LexLE [1, 2, 1, 1] [1, 1, 2, 1])) h)
              · intro q
                fin_cases q
                · exact by
                    constructor
                    · exact by
                        intro h
                        exact False.elim ((by decide : ¬ (LexLE [] [1, 2, 1, 1, 1] ∧ LexLE [1, 2, 1, 1, 1] [1, 1, 1, 2, 1])) h)
                    · intro q
                      fin_cases q
                      · exact by
                          intro h
                          exact False.elim ((by decide : ¬ (LexLE [] [1, 2, 1, 1, 1, 1] ∧ LexLE [1, 2, 1, 1, 1, 1] [1, 1, 1, 1, 2, 1])) h)
                      · exact by
                          intro _
                          exact k16t8_cover780
                · exact by
                    constructor
                    · exact by
                        intro _
                        exact k16t8_cover781
                    · intro q
                      fin_cases q
                      · exact by
                          intro _
                          exact k16t8_cover782
                · exact by
                    constructor
                    · exact by
                        intro _
                        exact k16t8_cover783
                    · intro q
                      exact Fin.elim0 q
          · exact by
              constructor
              · exact by
                  intro _
                  exact k16t8_cover784
              · intro q
                fin_cases q
                · exact by
                    constructor
                    · exact by
                        intro _
                        exact k16t8_cover786
                    · intro q
                      fin_cases q
                      · exact by
                          intro h
                          exact False.elim ((by decide : ¬ (LexLE [] [1, 2, 1, 2, 1, 1] ∧ LexLE [1, 2, 1, 2, 1, 1] [1, 1, 2, 1, 2, 1])) h)
                · exact by
                    constructor
                    · exact by
                        intro _
                        exact k16t8_cover787
                    · intro q
                      exact Fin.elim0 q
          · exact by
              constructor
              · exact by
                  intro _
                  exact k16t8_cover788
              · intro q
                fin_cases q
                · exact by
                    constructor
                    · exact by
                        intro _
                        exact k16t8_cover789
                    · intro q
                      exact Fin.elim0 q
          · exact by
              constructor
              · exact by
                  intro _
                  exact k16t8_cover790
              · intro q
                exact Fin.elim0 q
    · exact by
        constructor
        · exact by
            intro _
            exact k16t8_cover791
        · intro q
          fin_cases q
          · exact by
              constructor
              · exact by
                  intro _
                  exact k16t8_cover794
              · intro q
                fin_cases q
                · exact by
                    constructor
                    · exact by
                        intro h
                        exact False.elim ((by decide : ¬ (LexLE [] [1, 2, 2, 1, 1] ∧ LexLE [1, 2, 2, 1, 1] [1, 1, 2, 2, 1])) h)
                    · intro q
                      fin_cases q
                      · exact by
                          intro h
                          exact False.elim ((by decide : ¬ (LexLE [] [1, 2, 2, 1, 1, 1] ∧ LexLE [1, 2, 2, 1, 1, 1] [1, 1, 1, 2, 2, 1])) h)
                · exact by
                    constructor
                    · exact by
                        intro _
                        exact k16t8_cover796
                    · intro q
                      exact Fin.elim0 q
          · exact by
              constructor
              · exact by
                  intro _
                  exact k16t8_cover797
              · intro q
                fin_cases q
                · exact by
                    constructor
                    · exact by
                        intro _
                        exact k16t8_cover798
                    · intro q
                      exact Fin.elim0 q
          · exact by
              constructor
              · exact by
                  intro _
                  exact k16t8_cover799
              · intro q
                exact Fin.elim0 q
    · exact by
        constructor
        · exact by
            intro _
            exact k16t8_cover800
        · intro q
          fin_cases q
          · exact by
              constructor
              · exact by
                  intro _
                  exact k16t8_cover802
              · intro q
                fin_cases q
                · exact by
                    constructor
                    · exact by
                        intro h
                        exact False.elim ((by decide : ¬ (LexLE [] [1, 2, 3, 1, 1] ∧ LexLE [1, 2, 3, 1, 1] [1, 1, 3, 2, 1])) h)
                    · intro q
                      exact Fin.elim0 q
          · exact by
              constructor
              · exact by
                  intro _
                  exact k16t8_cover803
              · intro q
                exact Fin.elim0 q
    · exact by
        constructor
        · exact by
            intro _
            exact k16t8_cover804
        · intro q
          fin_cases q
          · exact by
              constructor
              · exact by
                  intro _
                  exact k16t8_cover805
              · intro q
                exact Fin.elim0 q
    · exact by
        constructor
        · exact by
            intro _
            exact k16t8_cover806
        · intro q
          exact Fin.elim0 q

private theorem k16t8_cover808 : ∀ P ∈ pathPatterns 1 0 [1, 3], HasCheckedCertificate 16 8 ([[], [1, 3], [1, 3]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [1, 3] [] ∧ LexLE [] [])) h)

private theorem k16t8_cover810 : ∀ P ∈ pathPatterns 0 0 [2], HasCheckedCertificate 16 8 ([[], [1, 3], [2], [2]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k16t8p360, Certificates.k16t8p360_check⟩

private theorem k16t8_cover809 : ∀ P ∈ pathPatterns 2 2 [2], HasCheckedCertificate 16 8 ([[], [1, 3], [2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [2] [] ∧ LexLE [] [])) h)
      · intro q
        fin_cases q
        · exact by
            intro h
            exact False.elim ((by decide : ¬ (LexLE [2] [1] ∧ LexLE [1] [1])) h)
        · exact by
            intro _
            exact k16t8_cover810

private theorem k16t8_cover811 : ∀ P ∈ pathPatterns 1 0 [2, 2], HasCheckedCertificate 16 8 ([[], [1, 3], [2, 2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [2, 2] [] ∧ LexLE [] [])) h)

private theorem k16t8_cover812 : ∀ P ∈ pathPatterns 2 1 [3], HasCheckedCertificate 16 8 ([[], [1, 3], [3]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [3] [] ∧ LexLE [] [])) h)
      · intro q
        fin_cases q
        · exact by
            intro h
            exact False.elim ((by decide : ¬ (LexLE [3] [1] ∧ LexLE [1] [1])) h)

private theorem k16t8_cover813 : ∀ P ∈ pathPatterns 2 0 [4], HasCheckedCertificate 16 8 ([[], [1, 3], [4]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [4] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k16t8_cover807 : ∀ P ∈ pathPatterns 4 4 [1, 3], HasCheckedCertificate 16 8 ([[], [1, 3]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [1, 3] [] ∧ LexLE [] [])) h)
      · intro q
        fin_cases q
        · exact by
            constructor
            · exact by
                intro h
                exact False.elim ((by decide : ¬ (LexLE [1, 3] [1] ∧ LexLE [1] [1])) h)
            · intro q
              fin_cases q
              · exact by
                  constructor
                  · exact by
                      intro h
                      exact False.elim ((by decide : ¬ (LexLE [1, 3] [1, 1] ∧ LexLE [1, 1] [1, 1])) h)
                  · intro q
                    fin_cases q
                    · exact by
                        intro h
                        exact False.elim ((by decide : ¬ (LexLE [1, 3] [1, 1, 1] ∧ LexLE [1, 1, 1] [1, 1, 1])) h)
                    · exact by
                        intro h
                        exact False.elim ((by decide : ¬ (LexLE [1, 3] [1, 1, 2] ∧ LexLE [1, 1, 2] [2, 1, 1])) h)
              · exact by
                  constructor
                  · exact by
                      intro h
                      exact False.elim ((by decide : ¬ (LexLE [1, 3] [1, 2] ∧ LexLE [1, 2] [2, 1])) h)
                  · intro q
                    fin_cases q
                    · exact by
                        intro h
                        exact False.elim ((by decide : ¬ (LexLE [1, 3] [1, 2, 1] ∧ LexLE [1, 2, 1] [1, 2, 1])) h)
              · exact by
                  constructor
                  · exact by
                      intro _
                      exact k16t8_cover808
                  · intro q
                    exact Fin.elim0 q
        · exact by
            constructor
            · exact by
                intro _
                exact k16t8_cover809
            · intro q
              fin_cases q
              · exact by
                  constructor
                  · exact by
                      intro h
                      exact False.elim ((by decide : ¬ (LexLE [1, 3] [2, 1] ∧ LexLE [2, 1] [1, 2])) h)
                  · intro q
                    fin_cases q
                    · exact by
                        intro h
                        exact False.elim ((by decide : ¬ (LexLE [1, 3] [2, 1, 1] ∧ LexLE [2, 1, 1] [1, 1, 2])) h)
              · exact by
                  constructor
                  · exact by
                      intro _
                      exact k16t8_cover811
                  · intro q
                    exact Fin.elim0 q
        · exact by
            constructor
            · exact by
                intro _
                exact k16t8_cover812
            · intro q
              fin_cases q
              · exact by
                  constructor
                  · exact by
                      intro h
                      exact False.elim ((by decide : ¬ (LexLE [1, 3] [3, 1] ∧ LexLE [3, 1] [1, 3])) h)
                  · intro q
                    exact Fin.elim0 q
        · exact by
            constructor
            · exact by
                intro _
                exact k16t8_cover813
            · intro q
              exact Fin.elim0 q

private theorem k16t8_cover815 : ∀ P ∈ pathPatterns 1 1 [2], HasCheckedCertificate 16 8 ([[], [1, 3, 1], [2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [2] [] ∧ LexLE [] [])) h)

private theorem k16t8_cover816 : ∀ P ∈ pathPatterns 1 0 [3], HasCheckedCertificate 16 8 ([[], [1, 3, 1], [3]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [3] [] ∧ LexLE [] [])) h)

private theorem k16t8_cover814 : ∀ P ∈ pathPatterns 3 3 [1, 3, 1], HasCheckedCertificate 16 8 ([[], [1, 3, 1]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [1, 3, 1] [] ∧ LexLE [] [])) h)
      · intro q
        fin_cases q
        · exact by
            constructor
            · exact by
                intro h
                exact False.elim ((by decide : ¬ (LexLE [1, 3, 1] [1] ∧ LexLE [1] [1])) h)
            · intro q
              fin_cases q
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [1, 3, 1] [1, 1] ∧ LexLE [1, 1] [1, 1])) h)
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [1, 3, 1] [1, 2] ∧ LexLE [1, 2] [2, 1])) h)
        · exact by
            constructor
            · exact by
                intro _
                exact k16t8_cover815
            · intro q
              fin_cases q
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [1, 3, 1] [2, 1] ∧ LexLE [2, 1] [1, 2])) h)
        · exact by
            constructor
            · exact by
                intro _
                exact k16t8_cover816
            · intro q
              exact Fin.elim0 q

private theorem k16t8_cover817 : ∀ P ∈ pathPatterns 1 0 [1, 3, 1, 1, 2], HasCheckedCertificate 16 8 ([[], [1, 3, 1, 1, 2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [1, 3, 1, 1, 2] [] ∧ LexLE [] [])) h)

private theorem k16t8_cover818 : ∀ P ∈ pathPatterns 2 1 [1, 3, 1, 2], HasCheckedCertificate 16 8 ([[], [1, 3, 1, 2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [1, 3, 1, 2] [] ∧ LexLE [] [])) h)
      · intro q
        fin_cases q
        · exact by
            intro h
            exact False.elim ((by decide : ¬ (LexLE [1, 3, 1, 2] [1] ∧ LexLE [1] [1])) h)

private theorem k16t8_cover819 : ∀ P ∈ pathPatterns 2 0 [1, 3, 1, 3], HasCheckedCertificate 16 8 ([[], [1, 3, 1, 3]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [1, 3, 1, 3] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k16t8_cover821 : ∀ P ∈ pathPatterns 1 0 [2], HasCheckedCertificate 16 8 ([[], [1, 3, 2], [2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [2] [] ∧ LexLE [] [])) h)

private theorem k16t8_cover820 : ∀ P ∈ pathPatterns 3 2 [1, 3, 2], HasCheckedCertificate 16 8 ([[], [1, 3, 2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [1, 3, 2] [] ∧ LexLE [] [])) h)
      · intro q
        fin_cases q
        · exact by
            constructor
            · exact by
                intro h
                exact False.elim ((by decide : ¬ (LexLE [1, 3, 2] [1] ∧ LexLE [1] [1])) h)
            · intro q
              fin_cases q
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [1, 3, 2] [1, 1] ∧ LexLE [1, 1] [1, 1])) h)
        · exact by
            constructor
            · exact by
                intro _
                exact k16t8_cover821
            · intro q
              exact Fin.elim0 q

private theorem k16t8_cover822 : ∀ P ∈ pathPatterns 2 0 [1, 3, 2, 2], HasCheckedCertificate 16 8 ([[], [1, 3, 2, 2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [1, 3, 2, 2] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k16t8_cover823 : ∀ P ∈ pathPatterns 3 1 [1, 3, 3], HasCheckedCertificate 16 8 ([[], [1, 3, 3]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [1, 3, 3] [] ∧ LexLE [] [])) h)
      · intro q
        fin_cases q
        · exact by
            constructor
            · exact by
                intro h
                exact False.elim ((by decide : ¬ (LexLE [1, 3, 3] [1] ∧ LexLE [1] [1])) h)
            · intro q
              exact Fin.elim0 q

private theorem k16t8_cover824 : ∀ P ∈ pathPatterns 2 0 [1, 3, 3, 1], HasCheckedCertificate 16 8 ([[], [1, 3, 3, 1]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [1, 3, 3, 1] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k16t8_cover825 : ∀ P ∈ pathPatterns 3 0 [1, 3, 4], HasCheckedCertificate 16 8 ([[], [1, 3, 4]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [1, 3, 4] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k16t8_cover827 : ∀ P ∈ pathPatterns 2 1 [2], HasCheckedCertificate 16 8 ([[], [1, 4], [2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [2] [] ∧ LexLE [] [])) h)
      · intro q
        fin_cases q
        · exact by
            intro h
            exact False.elim ((by decide : ¬ (LexLE [2] [1] ∧ LexLE [1] [1])) h)

private theorem k16t8_cover828 : ∀ P ∈ pathPatterns 2 0 [3], HasCheckedCertificate 16 8 ([[], [1, 4], [3]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [3] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k16t8_cover826 : ∀ P ∈ pathPatterns 4 3 [1, 4], HasCheckedCertificate 16 8 ([[], [1, 4]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [1, 4] [] ∧ LexLE [] [])) h)
      · intro q
        fin_cases q
        · exact by
            constructor
            · exact by
                intro h
                exact False.elim ((by decide : ¬ (LexLE [1, 4] [1] ∧ LexLE [1] [1])) h)
            · intro q
              fin_cases q
              · exact by
                  constructor
                  · exact by
                      intro h
                      exact False.elim ((by decide : ¬ (LexLE [1, 4] [1, 1] ∧ LexLE [1, 1] [1, 1])) h)
                  · intro q
                    fin_cases q
                    · exact by
                        intro h
                        exact False.elim ((by decide : ¬ (LexLE [1, 4] [1, 1, 1] ∧ LexLE [1, 1, 1] [1, 1, 1])) h)
              · exact by
                  constructor
                  · exact by
                      intro h
                      exact False.elim ((by decide : ¬ (LexLE [1, 4] [1, 2] ∧ LexLE [1, 2] [2, 1])) h)
                  · intro q
                    exact Fin.elim0 q
        · exact by
            constructor
            · exact by
                intro _
                exact k16t8_cover827
            · intro q
              fin_cases q
              · exact by
                  constructor
                  · exact by
                      intro h
                      exact False.elim ((by decide : ¬ (LexLE [1, 4] [2, 1] ∧ LexLE [2, 1] [1, 2])) h)
                  · intro q
                    exact Fin.elim0 q
        · exact by
            constructor
            · exact by
                intro _
                exact k16t8_cover828
            · intro q
              exact Fin.elim0 q

private theorem k16t8_cover830 : ∀ P ∈ pathPatterns 1 0 [2], HasCheckedCertificate 16 8 ([[], [1, 4, 1], [2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [2] [] ∧ LexLE [] [])) h)

private theorem k16t8_cover829 : ∀ P ∈ pathPatterns 3 2 [1, 4, 1], HasCheckedCertificate 16 8 ([[], [1, 4, 1]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [1, 4, 1] [] ∧ LexLE [] [])) h)
      · intro q
        fin_cases q
        · exact by
            constructor
            · exact by
                intro h
                exact False.elim ((by decide : ¬ (LexLE [1, 4, 1] [1] ∧ LexLE [1] [1])) h)
            · intro q
              fin_cases q
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [1, 4, 1] [1, 1] ∧ LexLE [1, 1] [1, 1])) h)
        · exact by
            constructor
            · exact by
                intro _
                exact k16t8_cover830
            · intro q
              exact Fin.elim0 q

private theorem k16t8_cover831 : ∀ P ∈ pathPatterns 2 0 [1, 4, 1, 2], HasCheckedCertificate 16 8 ([[], [1, 4, 1, 2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [1, 4, 1, 2] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k16t8_cover832 : ∀ P ∈ pathPatterns 3 1 [1, 4, 2], HasCheckedCertificate 16 8 ([[], [1, 4, 2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [1, 4, 2] [] ∧ LexLE [] [])) h)
      · intro q
        fin_cases q
        · exact by
            constructor
            · exact by
                intro h
                exact False.elim ((by decide : ¬ (LexLE [1, 4, 2] [1] ∧ LexLE [1] [1])) h)
            · intro q
              exact Fin.elim0 q

private theorem k16t8_cover833 : ∀ P ∈ pathPatterns 3 0 [1, 4, 3], HasCheckedCertificate 16 8 ([[], [1, 4, 3]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [1, 4, 3] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k16t8_cover835 : ∀ P ∈ pathPatterns 2 0 [2], HasCheckedCertificate 16 8 ([[], [1, 5], [2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [2] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k16t8_cover834 : ∀ P ∈ pathPatterns 4 2 [1, 5], HasCheckedCertificate 16 8 ([[], [1, 5]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [1, 5] [] ∧ LexLE [] [])) h)
      · intro q
        fin_cases q
        · exact by
            constructor
            · exact by
                intro h
                exact False.elim ((by decide : ¬ (LexLE [1, 5] [1] ∧ LexLE [1] [1])) h)
            · intro q
              fin_cases q
              · exact by
                  constructor
                  · exact by
                      intro h
                      exact False.elim ((by decide : ¬ (LexLE [1, 5] [1, 1] ∧ LexLE [1, 1] [1, 1])) h)
                  · intro q
                    exact Fin.elim0 q
        · exact by
            constructor
            · exact by
                intro _
                exact k16t8_cover835
            · intro q
              exact Fin.elim0 q

private theorem k16t8_cover836 : ∀ P ∈ pathPatterns 3 1 [1, 5, 1], HasCheckedCertificate 16 8 ([[], [1, 5, 1]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [1, 5, 1] [] ∧ LexLE [] [])) h)
      · intro q
        fin_cases q
        · exact by
            constructor
            · exact by
                intro h
                exact False.elim ((by decide : ¬ (LexLE [1, 5, 1] [1] ∧ LexLE [1] [1])) h)
            · intro q
              exact Fin.elim0 q

private theorem k16t8_cover837 : ∀ P ∈ pathPatterns 3 0 [1, 5, 2], HasCheckedCertificate 16 8 ([[], [1, 5, 2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [1, 5, 2] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k16t8_cover838 : ∀ P ∈ pathPatterns 4 1 [1, 6], HasCheckedCertificate 16 8 ([[], [1, 6]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [1, 6] [] ∧ LexLE [] [])) h)
      · intro q
        fin_cases q
        · exact by
            constructor
            · exact by
                intro h
                exact False.elim ((by decide : ¬ (LexLE [1, 6] [1] ∧ LexLE [1] [1])) h)
            · intro q
              exact Fin.elim0 q

private theorem k16t8_cover839 : ∀ P ∈ pathPatterns 3 0 [1, 6, 1], HasCheckedCertificate 16 8 ([[], [1, 6, 1]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [1, 6, 1] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k16t8_cover840 : ∀ P ∈ pathPatterns 4 0 [1, 7], HasCheckedCertificate 16 8 ([[], [1, 7]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [1, 7] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k16t8_seq539 : amountSequenceForall 5 7 (fun tail =>
    (LexLE [] ([1] ++ tail) ∧ LexLE ([1] ++ tail) ([1] ++ tail).reverse) →
    ∀ P ∈ pathPatterns (6 - ([1] ++ tail).length) (8 - ([1] ++ tail).sum) ([1] ++ tail),
      HasCheckedCertificate 16 8 ([[]] ++ (([1] ++ tail) :: P))) :=
by
  constructor
  · exact by
      intro _
      exact k16t8_cover540
  · intro q
    fin_cases q
    · exact k16t8_seq638

    · exact k16t8_seq756

    · exact by
        constructor
        · exact by
            intro _
            exact k16t8_cover807
        · intro q
          fin_cases q
          · exact by
              constructor
              · exact by
                  intro _
                  exact k16t8_cover814
              · intro q
                fin_cases q
                · exact by
                    constructor
                    · exact by
                        intro h
                        exact False.elim ((by decide : ¬ (LexLE [] [1, 3, 1, 1] ∧ LexLE [1, 3, 1, 1] [1, 1, 3, 1])) h)
                    · intro q
                      fin_cases q
                      · exact by
                          constructor
                          · exact by
                              intro h
                              exact False.elim ((by decide : ¬ (LexLE [] [1, 3, 1, 1, 1] ∧ LexLE [1, 3, 1, 1, 1] [1, 1, 1, 3, 1])) h)
                          · intro q
                            fin_cases q
                            · exact by
                                intro h
                                exact False.elim ((by decide : ¬ (LexLE [] [1, 3, 1, 1, 1, 1] ∧ LexLE [1, 3, 1, 1, 1, 1] [1, 1, 1, 1, 3, 1])) h)
                      · exact by
                          constructor
                          · exact by
                              intro _
                              exact k16t8_cover817
                          · intro q
                            exact Fin.elim0 q
                · exact by
                    constructor
                    · exact by
                        intro _
                        exact k16t8_cover818
                    · intro q
                      fin_cases q
                      · exact by
                          constructor
                          · exact by
                              intro h
                              exact False.elim ((by decide : ¬ (LexLE [] [1, 3, 1, 2, 1] ∧ LexLE [1, 3, 1, 2, 1] [1, 2, 1, 3, 1])) h)
                          · intro q
                            exact Fin.elim0 q
                · exact by
                    constructor
                    · exact by
                        intro _
                        exact k16t8_cover819
                    · intro q
                      exact Fin.elim0 q
          · exact by
              constructor
              · exact by
                  intro _
                  exact k16t8_cover820
              · intro q
                fin_cases q
                · exact by
                    constructor
                    · exact by
                        intro h
                        exact False.elim ((by decide : ¬ (LexLE [] [1, 3, 2, 1] ∧ LexLE [1, 3, 2, 1] [1, 2, 3, 1])) h)
                    · intro q
                      fin_cases q
                      · exact by
                          constructor
                          · exact by
                              intro h
                              exact False.elim ((by decide : ¬ (LexLE [] [1, 3, 2, 1, 1] ∧ LexLE [1, 3, 2, 1, 1] [1, 1, 2, 3, 1])) h)
                          · intro q
                            exact Fin.elim0 q
                · exact by
                    constructor
                    · exact by
                        intro _
                        exact k16t8_cover822
                    · intro q
                      exact Fin.elim0 q
          · exact by
              constructor
              · exact by
                  intro _
                  exact k16t8_cover823
              · intro q
                fin_cases q
                · exact by
                    constructor
                    · exact by
                        intro _
                        exact k16t8_cover824
                    · intro q
                      exact Fin.elim0 q
          · exact by
              constructor
              · exact by
                  intro _
                  exact k16t8_cover825
              · intro q
                exact Fin.elim0 q
    · exact by
        constructor
        · exact by
            intro _
            exact k16t8_cover826
        · intro q
          fin_cases q
          · exact by
              constructor
              · exact by
                  intro _
                  exact k16t8_cover829
              · intro q
                fin_cases q
                · exact by
                    constructor
                    · exact by
                        intro h
                        exact False.elim ((by decide : ¬ (LexLE [] [1, 4, 1, 1] ∧ LexLE [1, 4, 1, 1] [1, 1, 4, 1])) h)
                    · intro q
                      fin_cases q
                      · exact by
                          constructor
                          · exact by
                              intro h
                              exact False.elim ((by decide : ¬ (LexLE [] [1, 4, 1, 1, 1] ∧ LexLE [1, 4, 1, 1, 1] [1, 1, 1, 4, 1])) h)
                          · intro q
                            exact Fin.elim0 q
                · exact by
                    constructor
                    · exact by
                        intro _
                        exact k16t8_cover831
                    · intro q
                      exact Fin.elim0 q
          · exact by
              constructor
              · exact by
                  intro _
                  exact k16t8_cover832
              · intro q
                fin_cases q
                · exact by
                    constructor
                    · exact by
                        intro h
                        exact False.elim ((by decide : ¬ (LexLE [] [1, 4, 2, 1] ∧ LexLE [1, 4, 2, 1] [1, 2, 4, 1])) h)
                    · intro q
                      exact Fin.elim0 q
          · exact by
              constructor
              · exact by
                  intro _
                  exact k16t8_cover833
              · intro q
                exact Fin.elim0 q
    · exact by
        constructor
        · exact by
            intro _
            exact k16t8_cover834
        · intro q
          fin_cases q
          · exact by
              constructor
              · exact by
                  intro _
                  exact k16t8_cover836
              · intro q
                fin_cases q
                · exact by
                    constructor
                    · exact by
                        intro h
                        exact False.elim ((by decide : ¬ (LexLE [] [1, 5, 1, 1] ∧ LexLE [1, 5, 1, 1] [1, 1, 5, 1])) h)
                    · intro q
                      exact Fin.elim0 q
          · exact by
              constructor
              · exact by
                  intro _
                  exact k16t8_cover837
              · intro q
                exact Fin.elim0 q
    · exact by
        constructor
        · exact by
            intro _
            exact k16t8_cover838
        · intro q
          fin_cases q
          · exact by
              constructor
              · exact by
                  intro _
                  exact k16t8_cover839
              · intro q
                exact Fin.elim0 q
    · exact by
        constructor
        · exact by
            intro _
            exact k16t8_cover840
        · intro q
          exact Fin.elim0 q

private theorem k16t8_seq844 : amountSequenceForall 3 5 (fun tail =>
    (LexLE [2] ([1] ++ tail) ∧ LexLE ([1] ++ tail) ([1] ++ tail).reverse) →
    ∀ P ∈ pathPatterns (4 - ([1] ++ tail).length) (6 - ([1] ++ tail).sum) ([1] ++ tail),
      HasCheckedCertificate 16 8 ([[], [2]] ++ (([1] ++ tail) :: P))) :=
by
  constructor
  · exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [2] [1] ∧ LexLE [1] [1])) h)
  · intro q
    fin_cases q
    · exact by
        constructor
        · exact by
            intro h
            exact False.elim ((by decide : ¬ (LexLE [2] [1, 1] ∧ LexLE [1, 1] [1, 1])) h)
        · intro q
          fin_cases q
          · exact by
              constructor
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [2] [1, 1, 1] ∧ LexLE [1, 1, 1] [1, 1, 1])) h)
              · intro q
                fin_cases q
                · exact by
                    intro h
                    exact False.elim ((by decide : ¬ (LexLE [2] [1, 1, 1, 1] ∧ LexLE [1, 1, 1, 1] [1, 1, 1, 1])) h)
                · exact by
                    intro h
                    exact False.elim ((by decide : ¬ (LexLE [2] [1, 1, 1, 2] ∧ LexLE [1, 1, 1, 2] [2, 1, 1, 1])) h)
                · exact by
                    intro h
                    exact False.elim ((by decide : ¬ (LexLE [2] [1, 1, 1, 3] ∧ LexLE [1, 1, 1, 3] [3, 1, 1, 1])) h)
          · exact by
              constructor
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [2] [1, 1, 2] ∧ LexLE [1, 1, 2] [2, 1, 1])) h)
              · intro q
                fin_cases q
                · exact by
                    intro h
                    exact False.elim ((by decide : ¬ (LexLE [2] [1, 1, 2, 1] ∧ LexLE [1, 1, 2, 1] [1, 2, 1, 1])) h)
                · exact by
                    intro h
                    exact False.elim ((by decide : ¬ (LexLE [2] [1, 1, 2, 2] ∧ LexLE [1, 1, 2, 2] [2, 2, 1, 1])) h)
          · exact by
              constructor
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [2] [1, 1, 3] ∧ LexLE [1, 1, 3] [3, 1, 1])) h)
              · intro q
                fin_cases q
                · exact by
                    intro h
                    exact False.elim ((by decide : ¬ (LexLE [2] [1, 1, 3, 1] ∧ LexLE [1, 1, 3, 1] [1, 3, 1, 1])) h)
          · exact by
              constructor
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [2] [1, 1, 4] ∧ LexLE [1, 1, 4] [4, 1, 1])) h)
              · intro q
                exact Fin.elim0 q
    · exact by
        constructor
        · exact by
            intro h
            exact False.elim ((by decide : ¬ (LexLE [2] [1, 2] ∧ LexLE [1, 2] [2, 1])) h)
        · intro q
          fin_cases q
          · exact by
              constructor
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [2] [1, 2, 1] ∧ LexLE [1, 2, 1] [1, 2, 1])) h)
              · intro q
                fin_cases q
                · exact by
                    intro h
                    exact False.elim ((by decide : ¬ (LexLE [2] [1, 2, 1, 1] ∧ LexLE [1, 2, 1, 1] [1, 1, 2, 1])) h)
                · exact by
                    intro h
                    exact False.elim ((by decide : ¬ (LexLE [2] [1, 2, 1, 2] ∧ LexLE [1, 2, 1, 2] [2, 1, 2, 1])) h)
          · exact by
              constructor
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [2] [1, 2, 2] ∧ LexLE [1, 2, 2] [2, 2, 1])) h)
              · intro q
                fin_cases q
                · exact by
                    intro h
                    exact False.elim ((by decide : ¬ (LexLE [2] [1, 2, 2, 1] ∧ LexLE [1, 2, 2, 1] [1, 2, 2, 1])) h)
          · exact by
              constructor
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [2] [1, 2, 3] ∧ LexLE [1, 2, 3] [3, 2, 1])) h)
              · intro q
                exact Fin.elim0 q
    · exact by
        constructor
        · exact by
            intro h
            exact False.elim ((by decide : ¬ (LexLE [2] [1, 3] ∧ LexLE [1, 3] [3, 1])) h)
        · intro q
          fin_cases q
          · exact by
              constructor
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [2] [1, 3, 1] ∧ LexLE [1, 3, 1] [1, 3, 1])) h)
              · intro q
                fin_cases q
                · exact by
                    intro h
                    exact False.elim ((by decide : ¬ (LexLE [2] [1, 3, 1, 1] ∧ LexLE [1, 3, 1, 1] [1, 1, 3, 1])) h)
          · exact by
              constructor
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [2] [1, 3, 2] ∧ LexLE [1, 3, 2] [2, 3, 1])) h)
              · intro q
                exact Fin.elim0 q
    · exact by
        constructor
        · exact by
            intro h
            exact False.elim ((by decide : ¬ (LexLE [2] [1, 4] ∧ LexLE [1, 4] [4, 1])) h)
        · intro q
          fin_cases q
          · exact by
              constructor
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [2] [1, 4, 1] ∧ LexLE [1, 4, 1] [1, 4, 1])) h)
              · intro q
                exact Fin.elim0 q
    · exact by
        constructor
        · exact by
            intro h
            exact False.elim ((by decide : ¬ (LexLE [2] [1, 5] ∧ LexLE [1, 5] [5, 1])) h)
        · intro q
          exact Fin.elim0 q

private theorem k16t8_cover846 : ∀ P ∈ pathPatterns 1 2 [2], HasCheckedCertificate 16 8 ([[], [2], [2], [2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [2] [] ∧ LexLE [] [])) h)

private theorem k16t8_cover847 : ∀ P ∈ pathPatterns 0 0 [2, 2], HasCheckedCertificate 16 8 ([[], [2], [2], [2, 2]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k16t8p361, Certificates.k16t8p361_check⟩

private theorem k16t8_cover848 : ∀ P ∈ pathPatterns 1 1 [3], HasCheckedCertificate 16 8 ([[], [2], [2], [3]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [3] [] ∧ LexLE [] [])) h)

private theorem k16t8_cover849 : ∀ P ∈ pathPatterns 1 0 [4], HasCheckedCertificate 16 8 ([[], [2], [2], [4]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [4] [] ∧ LexLE [] [])) h)

private theorem k16t8_cover845 : ∀ P ∈ pathPatterns 3 4 [2], HasCheckedCertificate 16 8 ([[], [2], [2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [2] [] ∧ LexLE [] [])) h)
      · intro q
        fin_cases q
        · exact by
            constructor
            · exact by
                intro h
                exact False.elim ((by decide : ¬ (LexLE [2] [1] ∧ LexLE [1] [1])) h)
            · intro q
              fin_cases q
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [2] [1, 1] ∧ LexLE [1, 1] [1, 1])) h)
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [2] [1, 2] ∧ LexLE [1, 2] [2, 1])) h)
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [2] [1, 3] ∧ LexLE [1, 3] [3, 1])) h)
        · exact by
            constructor
            · exact by
                intro _
                exact k16t8_cover846
            · intro q
              fin_cases q
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [2] [2, 1] ∧ LexLE [2, 1] [1, 2])) h)
              · exact by
                  intro _
                  exact k16t8_cover847
        · exact by
            constructor
            · exact by
                intro _
                exact k16t8_cover848
            · intro q
              fin_cases q
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [2] [3, 1] ∧ LexLE [3, 1] [1, 3])) h)
        · exact by
            constructor
            · exact by
                intro _
                exact k16t8_cover849
            · intro q
              exact Fin.elim0 q

private theorem k16t8_cover850 : ∀ P ∈ pathPatterns 0 0 [2, 1, 1, 2], HasCheckedCertificate 16 8 ([[], [2], [2, 1, 1, 2]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k16t8p362, Certificates.k16t8p362_check⟩

private theorem k16t8_cover851 : ∀ P ∈ pathPatterns 1 1 [2, 1, 2], HasCheckedCertificate 16 8 ([[], [2], [2, 1, 2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [2, 1, 2] [] ∧ LexLE [] [])) h)

private theorem k16t8_cover852 : ∀ P ∈ pathPatterns 1 0 [2, 1, 3], HasCheckedCertificate 16 8 ([[], [2], [2, 1, 3]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [2, 1, 3] [] ∧ LexLE [] [])) h)

private theorem k16t8_cover853 : ∀ P ∈ pathPatterns 2 2 [2, 2], HasCheckedCertificate 16 8 ([[], [2], [2, 2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [2, 2] [] ∧ LexLE [] [])) h)
      · intro q
        fin_cases q
        · exact by
            intro h
            exact False.elim ((by decide : ¬ (LexLE [2, 2] [1] ∧ LexLE [1] [1])) h)
        · exact by
            intro h
            exact False.elim ((by decide : ¬ (LexLE [2, 2] [2] ∧ LexLE [2] [2])) h)

private theorem k16t8_cover854 : ∀ P ∈ pathPatterns 1 0 [2, 2, 2], HasCheckedCertificate 16 8 ([[], [2], [2, 2, 2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [2, 2, 2] [] ∧ LexLE [] [])) h)

private theorem k16t8_cover855 : ∀ P ∈ pathPatterns 2 1 [2, 3], HasCheckedCertificate 16 8 ([[], [2], [2, 3]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [2, 3] [] ∧ LexLE [] [])) h)
      · intro q
        fin_cases q
        · exact by
            intro h
            exact False.elim ((by decide : ¬ (LexLE [2, 3] [1] ∧ LexLE [1] [1])) h)

private theorem k16t8_cover856 : ∀ P ∈ pathPatterns 2 0 [2, 4], HasCheckedCertificate 16 8 ([[], [2], [2, 4]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [2, 4] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k16t8_cover858 : ∀ P ∈ pathPatterns 1 0 [3], HasCheckedCertificate 16 8 ([[], [2], [3], [3]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [3] [] ∧ LexLE [] [])) h)

private theorem k16t8_cover857 : ∀ P ∈ pathPatterns 3 3 [3], HasCheckedCertificate 16 8 ([[], [2], [3]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [3] [] ∧ LexLE [] [])) h)
      · intro q
        fin_cases q
        · exact by
            constructor
            · exact by
                intro h
                exact False.elim ((by decide : ¬ (LexLE [3] [1] ∧ LexLE [1] [1])) h)
            · intro q
              fin_cases q
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [3] [1, 1] ∧ LexLE [1, 1] [1, 1])) h)
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [3] [1, 2] ∧ LexLE [1, 2] [2, 1])) h)
        · exact by
            constructor
            · exact by
                intro h
                exact False.elim ((by decide : ¬ (LexLE [3] [2] ∧ LexLE [2] [2])) h)
            · intro q
              fin_cases q
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [3] [2, 1] ∧ LexLE [2, 1] [1, 2])) h)
        · exact by
            constructor
            · exact by
                intro _
                exact k16t8_cover858
            · intro q
              exact Fin.elim0 q

private theorem k16t8_cover859 : ∀ P ∈ pathPatterns 2 0 [3, 3], HasCheckedCertificate 16 8 ([[], [2], [3, 3]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [3, 3] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k16t8_cover860 : ∀ P ∈ pathPatterns 3 2 [4], HasCheckedCertificate 16 8 ([[], [2], [4]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [4] [] ∧ LexLE [] [])) h)
      · intro q
        fin_cases q
        · exact by
            constructor
            · exact by
                intro h
                exact False.elim ((by decide : ¬ (LexLE [4] [1] ∧ LexLE [1] [1])) h)
            · intro q
              fin_cases q
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [4] [1, 1] ∧ LexLE [1, 1] [1, 1])) h)
        · exact by
            constructor
            · exact by
                intro h
                exact False.elim ((by decide : ¬ (LexLE [4] [2] ∧ LexLE [2] [2])) h)
            · intro q
              exact Fin.elim0 q

private theorem k16t8_cover861 : ∀ P ∈ pathPatterns 3 1 [5], HasCheckedCertificate 16 8 ([[], [2], [5]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [5] [] ∧ LexLE [] [])) h)
      · intro q
        fin_cases q
        · exact by
            constructor
            · exact by
                intro h
                exact False.elim ((by decide : ¬ (LexLE [5] [1] ∧ LexLE [1] [1])) h)
            · intro q
              exact Fin.elim0 q

private theorem k16t8_cover862 : ∀ P ∈ pathPatterns 3 0 [6], HasCheckedCertificate 16 8 ([[], [2], [6]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [6] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k16t8_seq843 : amountSequenceForall 4 6 (fun tail =>
    (LexLE [2] ([] ++ tail) ∧ LexLE ([] ++ tail) ([] ++ tail).reverse) →
    ∀ P ∈ pathPatterns (4 - ([] ++ tail).length) (6 - ([] ++ tail).sum) ([] ++ tail),
      HasCheckedCertificate 16 8 ([[], [2]] ++ (([] ++ tail) :: P))) :=
by
  constructor
  · exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [2] [] ∧ LexLE [] [])) h)
  · intro q
    fin_cases q
    · exact k16t8_seq844

    · exact by
        constructor
        · exact by
            intro _
            exact k16t8_cover845
        · intro q
          fin_cases q
          · exact by
              constructor
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [2] [2, 1] ∧ LexLE [2, 1] [1, 2])) h)
              · intro q
                fin_cases q
                · exact by
                    constructor
                    · exact by
                        intro h
                        exact False.elim ((by decide : ¬ (LexLE [2] [2, 1, 1] ∧ LexLE [2, 1, 1] [1, 1, 2])) h)
                    · intro q
                      fin_cases q
                      · exact by
                          intro h
                          exact False.elim ((by decide : ¬ (LexLE [2] [2, 1, 1, 1] ∧ LexLE [2, 1, 1, 1] [1, 1, 1, 2])) h)
                      · exact by
                          intro _
                          exact k16t8_cover850
                · exact by
                    constructor
                    · exact by
                        intro _
                        exact k16t8_cover851
                    · intro q
                      fin_cases q
                      · exact by
                          intro h
                          exact False.elim ((by decide : ¬ (LexLE [2] [2, 1, 2, 1] ∧ LexLE [2, 1, 2, 1] [1, 2, 1, 2])) h)
                · exact by
                    constructor
                    · exact by
                        intro _
                        exact k16t8_cover852
                    · intro q
                      exact Fin.elim0 q
          · exact by
              constructor
              · exact by
                  intro _
                  exact k16t8_cover853
              · intro q
                fin_cases q
                · exact by
                    constructor
                    · exact by
                        intro h
                        exact False.elim ((by decide : ¬ (LexLE [2] [2, 2, 1] ∧ LexLE [2, 2, 1] [1, 2, 2])) h)
                    · intro q
                      fin_cases q
                      · exact by
                          intro h
                          exact False.elim ((by decide : ¬ (LexLE [2] [2, 2, 1, 1] ∧ LexLE [2, 2, 1, 1] [1, 1, 2, 2])) h)
                · exact by
                    constructor
                    · exact by
                        intro _
                        exact k16t8_cover854
                    · intro q
                      exact Fin.elim0 q
          · exact by
              constructor
              · exact by
                  intro _
                  exact k16t8_cover855
              · intro q
                fin_cases q
                · exact by
                    constructor
                    · exact by
                        intro h
                        exact False.elim ((by decide : ¬ (LexLE [2] [2, 3, 1] ∧ LexLE [2, 3, 1] [1, 3, 2])) h)
                    · intro q
                      exact Fin.elim0 q
          · exact by
              constructor
              · exact by
                  intro _
                  exact k16t8_cover856
              · intro q
                exact Fin.elim0 q
    · exact by
        constructor
        · exact by
            intro _
            exact k16t8_cover857
        · intro q
          fin_cases q
          · exact by
              constructor
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [2] [3, 1] ∧ LexLE [3, 1] [1, 3])) h)
              · intro q
                fin_cases q
                · exact by
                    constructor
                    · exact by
                        intro h
                        exact False.elim ((by decide : ¬ (LexLE [2] [3, 1, 1] ∧ LexLE [3, 1, 1] [1, 1, 3])) h)
                    · intro q
                      fin_cases q
                      · exact by
                          intro h
                          exact False.elim ((by decide : ¬ (LexLE [2] [3, 1, 1, 1] ∧ LexLE [3, 1, 1, 1] [1, 1, 1, 3])) h)
                · exact by
                    constructor
                    · exact by
                        intro h
                        exact False.elim ((by decide : ¬ (LexLE [2] [3, 1, 2] ∧ LexLE [3, 1, 2] [2, 1, 3])) h)
                    · intro q
                      exact Fin.elim0 q
          · exact by
              constructor
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [2] [3, 2] ∧ LexLE [3, 2] [2, 3])) h)
              · intro q
                fin_cases q
                · exact by
                    constructor
                    · exact by
                        intro h
                        exact False.elim ((by decide : ¬ (LexLE [2] [3, 2, 1] ∧ LexLE [3, 2, 1] [1, 2, 3])) h)
                    · intro q
                      exact Fin.elim0 q
          · exact by
              constructor
              · exact by
                  intro _
                  exact k16t8_cover859
              · intro q
                exact Fin.elim0 q
    · exact by
        constructor
        · exact by
            intro _
            exact k16t8_cover860
        · intro q
          fin_cases q
          · exact by
              constructor
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [2] [4, 1] ∧ LexLE [4, 1] [1, 4])) h)
              · intro q
                fin_cases q
                · exact by
                    constructor
                    · exact by
                        intro h
                        exact False.elim ((by decide : ¬ (LexLE [2] [4, 1, 1] ∧ LexLE [4, 1, 1] [1, 1, 4])) h)
                    · intro q
                      exact Fin.elim0 q
          · exact by
              constructor
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [2] [4, 2] ∧ LexLE [4, 2] [2, 4])) h)
              · intro q
                exact Fin.elim0 q
    · exact by
        constructor
        · exact by
            intro _
            exact k16t8_cover861
        · intro q
          fin_cases q
          · exact by
              constructor
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [2] [5, 1] ∧ LexLE [5, 1] [1, 5])) h)
              · intro q
                exact Fin.elim0 q
    · exact by
        constructor
        · exact by
            intro _
            exact k16t8_cover862
        · intro q
          exact Fin.elim0 q

private theorem k16t8_cover842 : ∀ P ∈ pathPatterns 5 6 [2], HasCheckedCertificate 16 8 ([[], [2]] ++ P) := by
  apply pathPatterns_forall_step
  exact k16t8_seq843


private theorem k16t8_cover864 : ∀ P ∈ pathPatterns 0 0 [2, 1, 1, 1, 1, 2], HasCheckedCertificate 16 8 ([[], [2, 1, 1, 1, 1, 2]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k16t8p363, Certificates.k16t8p363_check⟩

private theorem k16t8_cover865 : ∀ P ∈ pathPatterns 1 1 [2, 1, 1, 1, 2], HasCheckedCertificate 16 8 ([[], [2, 1, 1, 1, 2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [2, 1, 1, 1, 2] [] ∧ LexLE [] [])) h)

private theorem k16t8_cover866 : ∀ P ∈ pathPatterns 1 0 [2, 1, 1, 1, 3], HasCheckedCertificate 16 8 ([[], [2, 1, 1, 1, 3]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [2, 1, 1, 1, 3] [] ∧ LexLE [] [])) h)

private theorem k16t8_cover867 : ∀ P ∈ pathPatterns 2 2 [2, 1, 1, 2], HasCheckedCertificate 16 8 ([[], [2, 1, 1, 2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [2, 1, 1, 2] [] ∧ LexLE [] [])) h)
      · intro q
        fin_cases q
        · exact by
            intro h
            exact False.elim ((by decide : ¬ (LexLE [2, 1, 1, 2] [1] ∧ LexLE [1] [1])) h)
        · exact by
            intro h
            exact False.elim ((by decide : ¬ (LexLE [2, 1, 1, 2] [2] ∧ LexLE [2] [2])) h)

private theorem k16t8_cover868 : ∀ P ∈ pathPatterns 1 0 [2, 1, 1, 2, 2], HasCheckedCertificate 16 8 ([[], [2, 1, 1, 2, 2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [2, 1, 1, 2, 2] [] ∧ LexLE [] [])) h)

private theorem k16t8_cover869 : ∀ P ∈ pathPatterns 2 1 [2, 1, 1, 3], HasCheckedCertificate 16 8 ([[], [2, 1, 1, 3]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [2, 1, 1, 3] [] ∧ LexLE [] [])) h)
      · intro q
        fin_cases q
        · exact by
            intro h
            exact False.elim ((by decide : ¬ (LexLE [2, 1, 1, 3] [1] ∧ LexLE [1] [1])) h)

private theorem k16t8_cover870 : ∀ P ∈ pathPatterns 2 0 [2, 1, 1, 4], HasCheckedCertificate 16 8 ([[], [2, 1, 1, 4]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [2, 1, 1, 4] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k16t8_cover872 : ∀ P ∈ pathPatterns 1 0 [3], HasCheckedCertificate 16 8 ([[], [2, 1, 2], [3]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [3] [] ∧ LexLE [] [])) h)

private theorem k16t8_cover871 : ∀ P ∈ pathPatterns 3 3 [2, 1, 2], HasCheckedCertificate 16 8 ([[], [2, 1, 2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [2, 1, 2] [] ∧ LexLE [] [])) h)
      · intro q
        fin_cases q
        · exact by
            constructor
            · exact by
                intro h
                exact False.elim ((by decide : ¬ (LexLE [2, 1, 2] [1] ∧ LexLE [1] [1])) h)
            · intro q
              fin_cases q
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [2, 1, 2] [1, 1] ∧ LexLE [1, 1] [1, 1])) h)
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [2, 1, 2] [1, 2] ∧ LexLE [1, 2] [2, 1])) h)
        · exact by
            constructor
            · exact by
                intro h
                exact False.elim ((by decide : ¬ (LexLE [2, 1, 2] [2] ∧ LexLE [2] [2])) h)
            · intro q
              fin_cases q
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [2, 1, 2] [2, 1] ∧ LexLE [2, 1] [1, 2])) h)
        · exact by
            constructor
            · exact by
                intro _
                exact k16t8_cover872
            · intro q
              exact Fin.elim0 q

private theorem k16t8_cover873 : ∀ P ∈ pathPatterns 1 0 [2, 1, 2, 1, 2], HasCheckedCertificate 16 8 ([[], [2, 1, 2, 1, 2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [2, 1, 2, 1, 2] [] ∧ LexLE [] [])) h)

private theorem k16t8_cover874 : ∀ P ∈ pathPatterns 2 1 [2, 1, 2, 2], HasCheckedCertificate 16 8 ([[], [2, 1, 2, 2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [2, 1, 2, 2] [] ∧ LexLE [] [])) h)
      · intro q
        fin_cases q
        · exact by
            intro h
            exact False.elim ((by decide : ¬ (LexLE [2, 1, 2, 2] [1] ∧ LexLE [1] [1])) h)

private theorem k16t8_cover875 : ∀ P ∈ pathPatterns 2 0 [2, 1, 2, 3], HasCheckedCertificate 16 8 ([[], [2, 1, 2, 3]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [2, 1, 2, 3] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k16t8_cover876 : ∀ P ∈ pathPatterns 3 2 [2, 1, 3], HasCheckedCertificate 16 8 ([[], [2, 1, 3]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [2, 1, 3] [] ∧ LexLE [] [])) h)
      · intro q
        fin_cases q
        · exact by
            constructor
            · exact by
                intro h
                exact False.elim ((by decide : ¬ (LexLE [2, 1, 3] [1] ∧ LexLE [1] [1])) h)
            · intro q
              fin_cases q
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [2, 1, 3] [1, 1] ∧ LexLE [1, 1] [1, 1])) h)
        · exact by
            constructor
            · exact by
                intro h
                exact False.elim ((by decide : ¬ (LexLE [2, 1, 3] [2] ∧ LexLE [2] [2])) h)
            · intro q
              exact Fin.elim0 q

private theorem k16t8_cover877 : ∀ P ∈ pathPatterns 2 0 [2, 1, 3, 2], HasCheckedCertificate 16 8 ([[], [2, 1, 3, 2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [2, 1, 3, 2] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k16t8_cover878 : ∀ P ∈ pathPatterns 3 1 [2, 1, 4], HasCheckedCertificate 16 8 ([[], [2, 1, 4]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [2, 1, 4] [] ∧ LexLE [] [])) h)
      · intro q
        fin_cases q
        · exact by
            constructor
            · exact by
                intro h
                exact False.elim ((by decide : ¬ (LexLE [2, 1, 4] [1] ∧ LexLE [1] [1])) h)
            · intro q
              exact Fin.elim0 q

private theorem k16t8_cover879 : ∀ P ∈ pathPatterns 3 0 [2, 1, 5], HasCheckedCertificate 16 8 ([[], [2, 1, 5]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [2, 1, 5] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k16t8_seq863 : amountSequenceForall 4 5 (fun tail =>
    (LexLE [] ([2, 1] ++ tail) ∧ LexLE ([2, 1] ++ tail) ([2, 1] ++ tail).reverse) →
    ∀ P ∈ pathPatterns (6 - ([2, 1] ++ tail).length) (8 - ([2, 1] ++ tail).sum) ([2, 1] ++ tail),
      HasCheckedCertificate 16 8 ([[]] ++ (([2, 1] ++ tail) :: P))) :=
by
  constructor
  · exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [] [2, 1] ∧ LexLE [2, 1] [1, 2])) h)
  · intro q
    fin_cases q
    · exact by
        constructor
        · exact by
            intro h
            exact False.elim ((by decide : ¬ (LexLE [] [2, 1, 1] ∧ LexLE [2, 1, 1] [1, 1, 2])) h)
        · intro q
          fin_cases q
          · exact by
              constructor
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [] [2, 1, 1, 1] ∧ LexLE [2, 1, 1, 1] [1, 1, 1, 2])) h)
              · intro q
                fin_cases q
                · exact by
                    constructor
                    · exact by
                        intro h
                        exact False.elim ((by decide : ¬ (LexLE [] [2, 1, 1, 1, 1] ∧ LexLE [2, 1, 1, 1, 1] [1, 1, 1, 1, 2])) h)
                    · intro q
                      fin_cases q
                      · exact by
                          intro h
                          exact False.elim ((by decide : ¬ (LexLE [] [2, 1, 1, 1, 1, 1] ∧ LexLE [2, 1, 1, 1, 1, 1] [1, 1, 1, 1, 1, 2])) h)
                      · exact by
                          intro _
                          exact k16t8_cover864
                · exact by
                    constructor
                    · exact by
                        intro _
                        exact k16t8_cover865
                    · intro q
                      fin_cases q
                      · exact by
                          intro h
                          exact False.elim ((by decide : ¬ (LexLE [] [2, 1, 1, 1, 2, 1] ∧ LexLE [2, 1, 1, 1, 2, 1] [1, 2, 1, 1, 1, 2])) h)
                · exact by
                    constructor
                    · exact by
                        intro _
                        exact k16t8_cover866
                    · intro q
                      exact Fin.elim0 q
          · exact by
              constructor
              · exact by
                  intro _
                  exact k16t8_cover867
              · intro q
                fin_cases q
                · exact by
                    constructor
                    · exact by
                        intro h
                        exact False.elim ((by decide : ¬ (LexLE [] [2, 1, 1, 2, 1] ∧ LexLE [2, 1, 1, 2, 1] [1, 2, 1, 1, 2])) h)
                    · intro q
                      fin_cases q
                      · exact by
                          intro h
                          exact False.elim ((by decide : ¬ (LexLE [] [2, 1, 1, 2, 1, 1] ∧ LexLE [2, 1, 1, 2, 1, 1] [1, 1, 2, 1, 1, 2])) h)
                · exact by
                    constructor
                    · exact by
                        intro _
                        exact k16t8_cover868
                    · intro q
                      exact Fin.elim0 q
          · exact by
              constructor
              · exact by
                  intro _
                  exact k16t8_cover869
              · intro q
                fin_cases q
                · exact by
                    constructor
                    · exact by
                        intro h
                        exact False.elim ((by decide : ¬ (LexLE [] [2, 1, 1, 3, 1] ∧ LexLE [2, 1, 1, 3, 1] [1, 3, 1, 1, 2])) h)
                    · intro q
                      exact Fin.elim0 q
          · exact by
              constructor
              · exact by
                  intro _
                  exact k16t8_cover870
              · intro q
                exact Fin.elim0 q
    · exact by
        constructor
        · exact by
            intro _
            exact k16t8_cover871
        · intro q
          fin_cases q
          · exact by
              constructor
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [] [2, 1, 2, 1] ∧ LexLE [2, 1, 2, 1] [1, 2, 1, 2])) h)
              · intro q
                fin_cases q
                · exact by
                    constructor
                    · exact by
                        intro h
                        exact False.elim ((by decide : ¬ (LexLE [] [2, 1, 2, 1, 1] ∧ LexLE [2, 1, 2, 1, 1] [1, 1, 2, 1, 2])) h)
                    · intro q
                      fin_cases q
                      · exact by
                          intro h
                          exact False.elim ((by decide : ¬ (LexLE [] [2, 1, 2, 1, 1, 1] ∧ LexLE [2, 1, 2, 1, 1, 1] [1, 1, 1, 2, 1, 2])) h)
                · exact by
                    constructor
                    · exact by
                        intro _
                        exact k16t8_cover873
                    · intro q
                      exact Fin.elim0 q
          · exact by
              constructor
              · exact by
                  intro _
                  exact k16t8_cover874
              · intro q
                fin_cases q
                · exact by
                    constructor
                    · exact by
                        intro h
                        exact False.elim ((by decide : ¬ (LexLE [] [2, 1, 2, 2, 1] ∧ LexLE [2, 1, 2, 2, 1] [1, 2, 2, 1, 2])) h)
                    · intro q
                      exact Fin.elim0 q
          · exact by
              constructor
              · exact by
                  intro _
                  exact k16t8_cover875
              · intro q
                exact Fin.elim0 q
    · exact by
        constructor
        · exact by
            intro _
            exact k16t8_cover876
        · intro q
          fin_cases q
          · exact by
              constructor
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [] [2, 1, 3, 1] ∧ LexLE [2, 1, 3, 1] [1, 3, 1, 2])) h)
              · intro q
                fin_cases q
                · exact by
                    constructor
                    · exact by
                        intro h
                        exact False.elim ((by decide : ¬ (LexLE [] [2, 1, 3, 1, 1] ∧ LexLE [2, 1, 3, 1, 1] [1, 1, 3, 1, 2])) h)
                    · intro q
                      exact Fin.elim0 q
          · exact by
              constructor
              · exact by
                  intro _
                  exact k16t8_cover877
              · intro q
                exact Fin.elim0 q
    · exact by
        constructor
        · exact by
            intro _
            exact k16t8_cover878
        · intro q
          fin_cases q
          · exact by
              constructor
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [] [2, 1, 4, 1] ∧ LexLE [2, 1, 4, 1] [1, 4, 1, 2])) h)
              · intro q
                exact Fin.elim0 q
    · exact by
        constructor
        · exact by
            intro _
            exact k16t8_cover879
        · intro q
          exact Fin.elim0 q

private theorem k16t8_cover881 : ∀ P ∈ pathPatterns 1 0 [2, 2], HasCheckedCertificate 16 8 ([[], [2, 2], [2, 2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [2, 2] [] ∧ LexLE [] [])) h)

private theorem k16t8_cover882 : ∀ P ∈ pathPatterns 2 1 [3], HasCheckedCertificate 16 8 ([[], [2, 2], [3]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [3] [] ∧ LexLE [] [])) h)
      · intro q
        fin_cases q
        · exact by
            intro h
            exact False.elim ((by decide : ¬ (LexLE [3] [1] ∧ LexLE [1] [1])) h)

private theorem k16t8_cover883 : ∀ P ∈ pathPatterns 2 0 [4], HasCheckedCertificate 16 8 ([[], [2, 2], [4]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [4] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k16t8_cover880 : ∀ P ∈ pathPatterns 4 4 [2, 2], HasCheckedCertificate 16 8 ([[], [2, 2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [2, 2] [] ∧ LexLE [] [])) h)
      · intro q
        fin_cases q
        · exact by
            constructor
            · exact by
                intro h
                exact False.elim ((by decide : ¬ (LexLE [2, 2] [1] ∧ LexLE [1] [1])) h)
            · intro q
              fin_cases q
              · exact by
                  constructor
                  · exact by
                      intro h
                      exact False.elim ((by decide : ¬ (LexLE [2, 2] [1, 1] ∧ LexLE [1, 1] [1, 1])) h)
                  · intro q
                    fin_cases q
                    · exact by
                        intro h
                        exact False.elim ((by decide : ¬ (LexLE [2, 2] [1, 1, 1] ∧ LexLE [1, 1, 1] [1, 1, 1])) h)
                    · exact by
                        intro h
                        exact False.elim ((by decide : ¬ (LexLE [2, 2] [1, 1, 2] ∧ LexLE [1, 1, 2] [2, 1, 1])) h)
              · exact by
                  constructor
                  · exact by
                      intro h
                      exact False.elim ((by decide : ¬ (LexLE [2, 2] [1, 2] ∧ LexLE [1, 2] [2, 1])) h)
                  · intro q
                    fin_cases q
                    · exact by
                        intro h
                        exact False.elim ((by decide : ¬ (LexLE [2, 2] [1, 2, 1] ∧ LexLE [1, 2, 1] [1, 2, 1])) h)
              · exact by
                  constructor
                  · exact by
                      intro h
                      exact False.elim ((by decide : ¬ (LexLE [2, 2] [1, 3] ∧ LexLE [1, 3] [3, 1])) h)
                  · intro q
                    exact Fin.elim0 q
        · exact by
            constructor
            · exact by
                intro h
                exact False.elim ((by decide : ¬ (LexLE [2, 2] [2] ∧ LexLE [2] [2])) h)
            · intro q
              fin_cases q
              · exact by
                  constructor
                  · exact by
                      intro h
                      exact False.elim ((by decide : ¬ (LexLE [2, 2] [2, 1] ∧ LexLE [2, 1] [1, 2])) h)
                  · intro q
                    fin_cases q
                    · exact by
                        intro h
                        exact False.elim ((by decide : ¬ (LexLE [2, 2] [2, 1, 1] ∧ LexLE [2, 1, 1] [1, 1, 2])) h)
              · exact by
                  constructor
                  · exact by
                      intro _
                      exact k16t8_cover881
                  · intro q
                    exact Fin.elim0 q
        · exact by
            constructor
            · exact by
                intro _
                exact k16t8_cover882
            · intro q
              fin_cases q
              · exact by
                  constructor
                  · exact by
                      intro h
                      exact False.elim ((by decide : ¬ (LexLE [2, 2] [3, 1] ∧ LexLE [3, 1] [1, 3])) h)
                  · intro q
                    exact Fin.elim0 q
        · exact by
            constructor
            · exact by
                intro _
                exact k16t8_cover883
            · intro q
              exact Fin.elim0 q

private theorem k16t8_cover884 : ∀ P ∈ pathPatterns 2 0 [2, 2, 1, 3], HasCheckedCertificate 16 8 ([[], [2, 2, 1, 3]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [2, 2, 1, 3] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k16t8_cover885 : ∀ P ∈ pathPatterns 3 2 [2, 2, 2], HasCheckedCertificate 16 8 ([[], [2, 2, 2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [2, 2, 2] [] ∧ LexLE [] [])) h)
      · intro q
        fin_cases q
        · exact by
            constructor
            · exact by
                intro h
                exact False.elim ((by decide : ¬ (LexLE [2, 2, 2] [1] ∧ LexLE [1] [1])) h)
            · intro q
              fin_cases q
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [2, 2, 2] [1, 1] ∧ LexLE [1, 1] [1, 1])) h)
        · exact by
            constructor
            · exact by
                intro h
                exact False.elim ((by decide : ¬ (LexLE [2, 2, 2] [2] ∧ LexLE [2] [2])) h)
            · intro q
              exact Fin.elim0 q

private theorem k16t8_cover886 : ∀ P ∈ pathPatterns 2 0 [2, 2, 2, 2], HasCheckedCertificate 16 8 ([[], [2, 2, 2, 2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [2, 2, 2, 2] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k16t8_cover887 : ∀ P ∈ pathPatterns 3 1 [2, 2, 3], HasCheckedCertificate 16 8 ([[], [2, 2, 3]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [2, 2, 3] [] ∧ LexLE [] [])) h)
      · intro q
        fin_cases q
        · exact by
            constructor
            · exact by
                intro h
                exact False.elim ((by decide : ¬ (LexLE [2, 2, 3] [1] ∧ LexLE [1] [1])) h)
            · intro q
              exact Fin.elim0 q

private theorem k16t8_cover888 : ∀ P ∈ pathPatterns 3 0 [2, 2, 4], HasCheckedCertificate 16 8 ([[], [2, 2, 4]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [2, 2, 4] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k16t8_cover890 : ∀ P ∈ pathPatterns 2 0 [3], HasCheckedCertificate 16 8 ([[], [2, 3], [3]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [3] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k16t8_cover889 : ∀ P ∈ pathPatterns 4 3 [2, 3], HasCheckedCertificate 16 8 ([[], [2, 3]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [2, 3] [] ∧ LexLE [] [])) h)
      · intro q
        fin_cases q
        · exact by
            constructor
            · exact by
                intro h
                exact False.elim ((by decide : ¬ (LexLE [2, 3] [1] ∧ LexLE [1] [1])) h)
            · intro q
              fin_cases q
              · exact by
                  constructor
                  · exact by
                      intro h
                      exact False.elim ((by decide : ¬ (LexLE [2, 3] [1, 1] ∧ LexLE [1, 1] [1, 1])) h)
                  · intro q
                    fin_cases q
                    · exact by
                        intro h
                        exact False.elim ((by decide : ¬ (LexLE [2, 3] [1, 1, 1] ∧ LexLE [1, 1, 1] [1, 1, 1])) h)
              · exact by
                  constructor
                  · exact by
                      intro h
                      exact False.elim ((by decide : ¬ (LexLE [2, 3] [1, 2] ∧ LexLE [1, 2] [2, 1])) h)
                  · intro q
                    exact Fin.elim0 q
        · exact by
            constructor
            · exact by
                intro h
                exact False.elim ((by decide : ¬ (LexLE [2, 3] [2] ∧ LexLE [2] [2])) h)
            · intro q
              fin_cases q
              · exact by
                  constructor
                  · exact by
                      intro h
                      exact False.elim ((by decide : ¬ (LexLE [2, 3] [2, 1] ∧ LexLE [2, 1] [1, 2])) h)
                  · intro q
                    exact Fin.elim0 q
        · exact by
            constructor
            · exact by
                intro _
                exact k16t8_cover890
            · intro q
              exact Fin.elim0 q

private theorem k16t8_cover891 : ∀ P ∈ pathPatterns 3 1 [2, 3, 2], HasCheckedCertificate 16 8 ([[], [2, 3, 2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [2, 3, 2] [] ∧ LexLE [] [])) h)
      · intro q
        fin_cases q
        · exact by
            constructor
            · exact by
                intro h
                exact False.elim ((by decide : ¬ (LexLE [2, 3, 2] [1] ∧ LexLE [1] [1])) h)
            · intro q
              exact Fin.elim0 q

private theorem k16t8_cover892 : ∀ P ∈ pathPatterns 3 0 [2, 3, 3], HasCheckedCertificate 16 8 ([[], [2, 3, 3]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [2, 3, 3] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k16t8_cover893 : ∀ P ∈ pathPatterns 4 2 [2, 4], HasCheckedCertificate 16 8 ([[], [2, 4]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [2, 4] [] ∧ LexLE [] [])) h)
      · intro q
        fin_cases q
        · exact by
            constructor
            · exact by
                intro h
                exact False.elim ((by decide : ¬ (LexLE [2, 4] [1] ∧ LexLE [1] [1])) h)
            · intro q
              fin_cases q
              · exact by
                  constructor
                  · exact by
                      intro h
                      exact False.elim ((by decide : ¬ (LexLE [2, 4] [1, 1] ∧ LexLE [1, 1] [1, 1])) h)
                  · intro q
                    exact Fin.elim0 q
        · exact by
            constructor
            · exact by
                intro h
                exact False.elim ((by decide : ¬ (LexLE [2, 4] [2] ∧ LexLE [2] [2])) h)
            · intro q
              exact Fin.elim0 q

private theorem k16t8_cover894 : ∀ P ∈ pathPatterns 3 0 [2, 4, 2], HasCheckedCertificate 16 8 ([[], [2, 4, 2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [2, 4, 2] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k16t8_cover895 : ∀ P ∈ pathPatterns 4 1 [2, 5], HasCheckedCertificate 16 8 ([[], [2, 5]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [2, 5] [] ∧ LexLE [] [])) h)
      · intro q
        fin_cases q
        · exact by
            constructor
            · exact by
                intro h
                exact False.elim ((by decide : ¬ (LexLE [2, 5] [1] ∧ LexLE [1] [1])) h)
            · intro q
              exact Fin.elim0 q

private theorem k16t8_cover896 : ∀ P ∈ pathPatterns 4 0 [2, 6], HasCheckedCertificate 16 8 ([[], [2, 6]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [2, 6] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k16t8_seq841 : amountSequenceForall 5 6 (fun tail =>
    (LexLE [] ([2] ++ tail) ∧ LexLE ([2] ++ tail) ([2] ++ tail).reverse) →
    ∀ P ∈ pathPatterns (6 - ([2] ++ tail).length) (8 - ([2] ++ tail).sum) ([2] ++ tail),
      HasCheckedCertificate 16 8 ([[]] ++ (([2] ++ tail) :: P))) :=
by
  constructor
  · exact by
      intro _
      exact k16t8_cover842
  · intro q
    fin_cases q
    · exact k16t8_seq863

    · exact by
        constructor
        · exact by
            intro _
            exact k16t8_cover880
        · intro q
          fin_cases q
          · exact by
              constructor
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [] [2, 2, 1] ∧ LexLE [2, 2, 1] [1, 2, 2])) h)
              · intro q
                fin_cases q
                · exact by
                    constructor
                    · exact by
                        intro h
                        exact False.elim ((by decide : ¬ (LexLE [] [2, 2, 1, 1] ∧ LexLE [2, 2, 1, 1] [1, 1, 2, 2])) h)
                    · intro q
                      fin_cases q
                      · exact by
                          constructor
                          · exact by
                              intro h
                              exact False.elim ((by decide : ¬ (LexLE [] [2, 2, 1, 1, 1] ∧ LexLE [2, 2, 1, 1, 1] [1, 1, 1, 2, 2])) h)
                          · intro q
                            fin_cases q
                            · exact by
                                intro h
                                exact False.elim ((by decide : ¬ (LexLE [] [2, 2, 1, 1, 1, 1] ∧ LexLE [2, 2, 1, 1, 1, 1] [1, 1, 1, 1, 2, 2])) h)
                      · exact by
                          constructor
                          · exact by
                              intro h
                              exact False.elim ((by decide : ¬ (LexLE [] [2, 2, 1, 1, 2] ∧ LexLE [2, 2, 1, 1, 2] [2, 1, 1, 2, 2])) h)
                          · intro q
                            exact Fin.elim0 q
                · exact by
                    constructor
                    · exact by
                        intro h
                        exact False.elim ((by decide : ¬ (LexLE [] [2, 2, 1, 2] ∧ LexLE [2, 2, 1, 2] [2, 1, 2, 2])) h)
                    · intro q
                      fin_cases q
                      · exact by
                          constructor
                          · exact by
                              intro h
                              exact False.elim ((by decide : ¬ (LexLE [] [2, 2, 1, 2, 1] ∧ LexLE [2, 2, 1, 2, 1] [1, 2, 1, 2, 2])) h)
                          · intro q
                            exact Fin.elim0 q
                · exact by
                    constructor
                    · exact by
                        intro _
                        exact k16t8_cover884
                    · intro q
                      exact Fin.elim0 q
          · exact by
              constructor
              · exact by
                  intro _
                  exact k16t8_cover885
              · intro q
                fin_cases q
                · exact by
                    constructor
                    · exact by
                        intro h
                        exact False.elim ((by decide : ¬ (LexLE [] [2, 2, 2, 1] ∧ LexLE [2, 2, 2, 1] [1, 2, 2, 2])) h)
                    · intro q
                      fin_cases q
                      · exact by
                          constructor
                          · exact by
                              intro h
                              exact False.elim ((by decide : ¬ (LexLE [] [2, 2, 2, 1, 1] ∧ LexLE [2, 2, 2, 1, 1] [1, 1, 2, 2, 2])) h)
                          · intro q
                            exact Fin.elim0 q
                · exact by
                    constructor
                    · exact by
                        intro _
                        exact k16t8_cover886
                    · intro q
                      exact Fin.elim0 q
          · exact by
              constructor
              · exact by
                  intro _
                  exact k16t8_cover887
              · intro q
                fin_cases q
                · exact by
                    constructor
                    · exact by
                        intro h
                        exact False.elim ((by decide : ¬ (LexLE [] [2, 2, 3, 1] ∧ LexLE [2, 2, 3, 1] [1, 3, 2, 2])) h)
                    · intro q
                      exact Fin.elim0 q
          · exact by
              constructor
              · exact by
                  intro _
                  exact k16t8_cover888
              · intro q
                exact Fin.elim0 q
    · exact by
        constructor
        · exact by
            intro _
            exact k16t8_cover889
        · intro q
          fin_cases q
          · exact by
              constructor
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [] [2, 3, 1] ∧ LexLE [2, 3, 1] [1, 3, 2])) h)
              · intro q
                fin_cases q
                · exact by
                    constructor
                    · exact by
                        intro h
                        exact False.elim ((by decide : ¬ (LexLE [] [2, 3, 1, 1] ∧ LexLE [2, 3, 1, 1] [1, 1, 3, 2])) h)
                    · intro q
                      fin_cases q
                      · exact by
                          constructor
                          · exact by
                              intro h
                              exact False.elim ((by decide : ¬ (LexLE [] [2, 3, 1, 1, 1] ∧ LexLE [2, 3, 1, 1, 1] [1, 1, 1, 3, 2])) h)
                          · intro q
                            exact Fin.elim0 q
                · exact by
                    constructor
                    · exact by
                        intro h
                        exact False.elim ((by decide : ¬ (LexLE [] [2, 3, 1, 2] ∧ LexLE [2, 3, 1, 2] [2, 1, 3, 2])) h)
                    · intro q
                      exact Fin.elim0 q
          · exact by
              constructor
              · exact by
                  intro _
                  exact k16t8_cover891
              · intro q
                fin_cases q
                · exact by
                    constructor
                    · exact by
                        intro h
                        exact False.elim ((by decide : ¬ (LexLE [] [2, 3, 2, 1] ∧ LexLE [2, 3, 2, 1] [1, 2, 3, 2])) h)
                    · intro q
                      exact Fin.elim0 q
          · exact by
              constructor
              · exact by
                  intro _
                  exact k16t8_cover892
              · intro q
                exact Fin.elim0 q
    · exact by
        constructor
        · exact by
            intro _
            exact k16t8_cover893
        · intro q
          fin_cases q
          · exact by
              constructor
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [] [2, 4, 1] ∧ LexLE [2, 4, 1] [1, 4, 2])) h)
              · intro q
                fin_cases q
                · exact by
                    constructor
                    · exact by
                        intro h
                        exact False.elim ((by decide : ¬ (LexLE [] [2, 4, 1, 1] ∧ LexLE [2, 4, 1, 1] [1, 1, 4, 2])) h)
                    · intro q
                      exact Fin.elim0 q
          · exact by
              constructor
              · exact by
                  intro _
                  exact k16t8_cover894
              · intro q
                exact Fin.elim0 q
    · exact by
        constructor
        · exact by
            intro _
            exact k16t8_cover895
        · intro q
          fin_cases q
          · exact by
              constructor
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [] [2, 5, 1] ∧ LexLE [2, 5, 1] [1, 5, 2])) h)
              · intro q
                exact Fin.elim0 q
    · exact by
        constructor
        · exact by
            intro _
            exact k16t8_cover896
        · intro q
          exact Fin.elim0 q

private theorem k16t8_cover900 : ∀ P ∈ pathPatterns 3 2 [3], HasCheckedCertificate 16 8 ([[], [3], [3]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [3] [] ∧ LexLE [] [])) h)
      · intro q
        fin_cases q
        · exact by
            constructor
            · exact by
                intro h
                exact False.elim ((by decide : ¬ (LexLE [3] [1] ∧ LexLE [1] [1])) h)
            · intro q
              fin_cases q
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [3] [1, 1] ∧ LexLE [1, 1] [1, 1])) h)
        · exact by
            constructor
            · exact by
                intro h
                exact False.elim ((by decide : ¬ (LexLE [3] [2] ∧ LexLE [2] [2])) h)
            · intro q
              exact Fin.elim0 q

private theorem k16t8_cover901 : ∀ P ∈ pathPatterns 3 1 [4], HasCheckedCertificate 16 8 ([[], [3], [4]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [4] [] ∧ LexLE [] [])) h)
      · intro q
        fin_cases q
        · exact by
            constructor
            · exact by
                intro h
                exact False.elim ((by decide : ¬ (LexLE [4] [1] ∧ LexLE [1] [1])) h)
            · intro q
              exact Fin.elim0 q

private theorem k16t8_cover902 : ∀ P ∈ pathPatterns 3 0 [5], HasCheckedCertificate 16 8 ([[], [3], [5]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [5] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k16t8_seq899 : amountSequenceForall 4 5 (fun tail =>
    (LexLE [3] ([] ++ tail) ∧ LexLE ([] ++ tail) ([] ++ tail).reverse) →
    ∀ P ∈ pathPatterns (4 - ([] ++ tail).length) (5 - ([] ++ tail).sum) ([] ++ tail),
      HasCheckedCertificate 16 8 ([[], [3]] ++ (([] ++ tail) :: P))) :=
by
  constructor
  · exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [3] [] ∧ LexLE [] [])) h)
  · intro q
    fin_cases q
    · exact by
        constructor
        · exact by
            intro h
            exact False.elim ((by decide : ¬ (LexLE [3] [1] ∧ LexLE [1] [1])) h)
        · intro q
          fin_cases q
          · exact by
              constructor
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [3] [1, 1] ∧ LexLE [1, 1] [1, 1])) h)
              · intro q
                fin_cases q
                · exact by
                    constructor
                    · exact by
                        intro h
                        exact False.elim ((by decide : ¬ (LexLE [3] [1, 1, 1] ∧ LexLE [1, 1, 1] [1, 1, 1])) h)
                    · intro q
                      fin_cases q
                      · exact by
                          intro h
                          exact False.elim ((by decide : ¬ (LexLE [3] [1, 1, 1, 1] ∧ LexLE [1, 1, 1, 1] [1, 1, 1, 1])) h)
                      · exact by
                          intro h
                          exact False.elim ((by decide : ¬ (LexLE [3] [1, 1, 1, 2] ∧ LexLE [1, 1, 1, 2] [2, 1, 1, 1])) h)
                · exact by
                    constructor
                    · exact by
                        intro h
                        exact False.elim ((by decide : ¬ (LexLE [3] [1, 1, 2] ∧ LexLE [1, 1, 2] [2, 1, 1])) h)
                    · intro q
                      fin_cases q
                      · exact by
                          intro h
                          exact False.elim ((by decide : ¬ (LexLE [3] [1, 1, 2, 1] ∧ LexLE [1, 1, 2, 1] [1, 2, 1, 1])) h)
                · exact by
                    constructor
                    · exact by
                        intro h
                        exact False.elim ((by decide : ¬ (LexLE [3] [1, 1, 3] ∧ LexLE [1, 1, 3] [3, 1, 1])) h)
                    · intro q
                      exact Fin.elim0 q
          · exact by
              constructor
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [3] [1, 2] ∧ LexLE [1, 2] [2, 1])) h)
              · intro q
                fin_cases q
                · exact by
                    constructor
                    · exact by
                        intro h
                        exact False.elim ((by decide : ¬ (LexLE [3] [1, 2, 1] ∧ LexLE [1, 2, 1] [1, 2, 1])) h)
                    · intro q
                      fin_cases q
                      · exact by
                          intro h
                          exact False.elim ((by decide : ¬ (LexLE [3] [1, 2, 1, 1] ∧ LexLE [1, 2, 1, 1] [1, 1, 2, 1])) h)
                · exact by
                    constructor
                    · exact by
                        intro h
                        exact False.elim ((by decide : ¬ (LexLE [3] [1, 2, 2] ∧ LexLE [1, 2, 2] [2, 2, 1])) h)
                    · intro q
                      exact Fin.elim0 q
          · exact by
              constructor
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [3] [1, 3] ∧ LexLE [1, 3] [3, 1])) h)
              · intro q
                fin_cases q
                · exact by
                    constructor
                    · exact by
                        intro h
                        exact False.elim ((by decide : ¬ (LexLE [3] [1, 3, 1] ∧ LexLE [1, 3, 1] [1, 3, 1])) h)
                    · intro q
                      exact Fin.elim0 q
          · exact by
              constructor
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [3] [1, 4] ∧ LexLE [1, 4] [4, 1])) h)
              · intro q
                exact Fin.elim0 q
    · exact by
        constructor
        · exact by
            intro h
            exact False.elim ((by decide : ¬ (LexLE [3] [2] ∧ LexLE [2] [2])) h)
        · intro q
          fin_cases q
          · exact by
              constructor
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [3] [2, 1] ∧ LexLE [2, 1] [1, 2])) h)
              · intro q
                fin_cases q
                · exact by
                    constructor
                    · exact by
                        intro h
                        exact False.elim ((by decide : ¬ (LexLE [3] [2, 1, 1] ∧ LexLE [2, 1, 1] [1, 1, 2])) h)
                    · intro q
                      fin_cases q
                      · exact by
                          intro h
                          exact False.elim ((by decide : ¬ (LexLE [3] [2, 1, 1, 1] ∧ LexLE [2, 1, 1, 1] [1, 1, 1, 2])) h)
                · exact by
                    constructor
                    · exact by
                        intro h
                        exact False.elim ((by decide : ¬ (LexLE [3] [2, 1, 2] ∧ LexLE [2, 1, 2] [2, 1, 2])) h)
                    · intro q
                      exact Fin.elim0 q
          · exact by
              constructor
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [3] [2, 2] ∧ LexLE [2, 2] [2, 2])) h)
              · intro q
                fin_cases q
                · exact by
                    constructor
                    · exact by
                        intro h
                        exact False.elim ((by decide : ¬ (LexLE [3] [2, 2, 1] ∧ LexLE [2, 2, 1] [1, 2, 2])) h)
                    · intro q
                      exact Fin.elim0 q
          · exact by
              constructor
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [3] [2, 3] ∧ LexLE [2, 3] [3, 2])) h)
              · intro q
                exact Fin.elim0 q
    · exact by
        constructor
        · exact by
            intro _
            exact k16t8_cover900
        · intro q
          fin_cases q
          · exact by
              constructor
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [3] [3, 1] ∧ LexLE [3, 1] [1, 3])) h)
              · intro q
                fin_cases q
                · exact by
                    constructor
                    · exact by
                        intro h
                        exact False.elim ((by decide : ¬ (LexLE [3] [3, 1, 1] ∧ LexLE [3, 1, 1] [1, 1, 3])) h)
                    · intro q
                      exact Fin.elim0 q
          · exact by
              constructor
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [3] [3, 2] ∧ LexLE [3, 2] [2, 3])) h)
              · intro q
                exact Fin.elim0 q
    · exact by
        constructor
        · exact by
            intro _
            exact k16t8_cover901
        · intro q
          fin_cases q
          · exact by
              constructor
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [3] [4, 1] ∧ LexLE [4, 1] [1, 4])) h)
              · intro q
                exact Fin.elim0 q
    · exact by
        constructor
        · exact by
            intro _
            exact k16t8_cover902
        · intro q
          exact Fin.elim0 q

private theorem k16t8_cover898 : ∀ P ∈ pathPatterns 5 5 [3], HasCheckedCertificate 16 8 ([[], [3]] ++ P) := by
  apply pathPatterns_forall_step
  exact k16t8_seq899


private theorem k16t8_cover903 : ∀ P ∈ pathPatterns 2 0 [3, 1, 1, 3], HasCheckedCertificate 16 8 ([[], [3, 1, 1, 3]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [3, 1, 1, 3] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k16t8_cover904 : ∀ P ∈ pathPatterns 3 1 [3, 1, 3], HasCheckedCertificate 16 8 ([[], [3, 1, 3]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [3, 1, 3] [] ∧ LexLE [] [])) h)
      · intro q
        fin_cases q
        · exact by
            constructor
            · exact by
                intro h
                exact False.elim ((by decide : ¬ (LexLE [3, 1, 3] [1] ∧ LexLE [1] [1])) h)
            · intro q
              exact Fin.elim0 q

private theorem k16t8_cover905 : ∀ P ∈ pathPatterns 3 0 [3, 1, 4], HasCheckedCertificate 16 8 ([[], [3, 1, 4]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [3, 1, 4] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k16t8_cover906 : ∀ P ∈ pathPatterns 3 0 [3, 2, 3], HasCheckedCertificate 16 8 ([[], [3, 2, 3]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [3, 2, 3] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k16t8_cover907 : ∀ P ∈ pathPatterns 4 2 [3, 3], HasCheckedCertificate 16 8 ([[], [3, 3]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [3, 3] [] ∧ LexLE [] [])) h)
      · intro q
        fin_cases q
        · exact by
            constructor
            · exact by
                intro h
                exact False.elim ((by decide : ¬ (LexLE [3, 3] [1] ∧ LexLE [1] [1])) h)
            · intro q
              fin_cases q
              · exact by
                  constructor
                  · exact by
                      intro h
                      exact False.elim ((by decide : ¬ (LexLE [3, 3] [1, 1] ∧ LexLE [1, 1] [1, 1])) h)
                  · intro q
                    exact Fin.elim0 q
        · exact by
            constructor
            · exact by
                intro h
                exact False.elim ((by decide : ¬ (LexLE [3, 3] [2] ∧ LexLE [2] [2])) h)
            · intro q
              exact Fin.elim0 q

private theorem k16t8_cover908 : ∀ P ∈ pathPatterns 4 1 [3, 4], HasCheckedCertificate 16 8 ([[], [3, 4]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [3, 4] [] ∧ LexLE [] [])) h)
      · intro q
        fin_cases q
        · exact by
            constructor
            · exact by
                intro h
                exact False.elim ((by decide : ¬ (LexLE [3, 4] [1] ∧ LexLE [1] [1])) h)
            · intro q
              exact Fin.elim0 q

private theorem k16t8_cover909 : ∀ P ∈ pathPatterns 4 0 [3, 5], HasCheckedCertificate 16 8 ([[], [3, 5]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [3, 5] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k16t8_seq897 : amountSequenceForall 5 5 (fun tail =>
    (LexLE [] ([3] ++ tail) ∧ LexLE ([3] ++ tail) ([3] ++ tail).reverse) →
    ∀ P ∈ pathPatterns (6 - ([3] ++ tail).length) (8 - ([3] ++ tail).sum) ([3] ++ tail),
      HasCheckedCertificate 16 8 ([[]] ++ (([3] ++ tail) :: P))) :=
by
  constructor
  · exact by
      intro _
      exact k16t8_cover898
  · intro q
    fin_cases q
    · exact by
        constructor
        · exact by
            intro h
            exact False.elim ((by decide : ¬ (LexLE [] [3, 1] ∧ LexLE [3, 1] [1, 3])) h)
        · intro q
          fin_cases q
          · exact by
              constructor
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [] [3, 1, 1] ∧ LexLE [3, 1, 1] [1, 1, 3])) h)
              · intro q
                fin_cases q
                · exact by
                    constructor
                    · exact by
                        intro h
                        exact False.elim ((by decide : ¬ (LexLE [] [3, 1, 1, 1] ∧ LexLE [3, 1, 1, 1] [1, 1, 1, 3])) h)
                    · intro q
                      fin_cases q
                      · exact by
                          constructor
                          · exact by
                              intro h
                              exact False.elim ((by decide : ¬ (LexLE [] [3, 1, 1, 1, 1] ∧ LexLE [3, 1, 1, 1, 1] [1, 1, 1, 1, 3])) h)
                          · intro q
                            fin_cases q
                            · exact by
                                intro h
                                exact False.elim ((by decide : ¬ (LexLE [] [3, 1, 1, 1, 1, 1] ∧ LexLE [3, 1, 1, 1, 1, 1] [1, 1, 1, 1, 1, 3])) h)
                      · exact by
                          constructor
                          · exact by
                              intro h
                              exact False.elim ((by decide : ¬ (LexLE [] [3, 1, 1, 1, 2] ∧ LexLE [3, 1, 1, 1, 2] [2, 1, 1, 1, 3])) h)
                          · intro q
                            exact Fin.elim0 q
                · exact by
                    constructor
                    · exact by
                        intro h
                        exact False.elim ((by decide : ¬ (LexLE [] [3, 1, 1, 2] ∧ LexLE [3, 1, 1, 2] [2, 1, 1, 3])) h)
                    · intro q
                      fin_cases q
                      · exact by
                          constructor
                          · exact by
                              intro h
                              exact False.elim ((by decide : ¬ (LexLE [] [3, 1, 1, 2, 1] ∧ LexLE [3, 1, 1, 2, 1] [1, 2, 1, 1, 3])) h)
                          · intro q
                            exact Fin.elim0 q
                · exact by
                    constructor
                    · exact by
                        intro _
                        exact k16t8_cover903
                    · intro q
                      exact Fin.elim0 q
          · exact by
              constructor
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [] [3, 1, 2] ∧ LexLE [3, 1, 2] [2, 1, 3])) h)
              · intro q
                fin_cases q
                · exact by
                    constructor
                    · exact by
                        intro h
                        exact False.elim ((by decide : ¬ (LexLE [] [3, 1, 2, 1] ∧ LexLE [3, 1, 2, 1] [1, 2, 1, 3])) h)
                    · intro q
                      fin_cases q
                      · exact by
                          constructor
                          · exact by
                              intro h
                              exact False.elim ((by decide : ¬ (LexLE [] [3, 1, 2, 1, 1] ∧ LexLE [3, 1, 2, 1, 1] [1, 1, 2, 1, 3])) h)
                          · intro q
                            exact Fin.elim0 q
                · exact by
                    constructor
                    · exact by
                        intro h
                        exact False.elim ((by decide : ¬ (LexLE [] [3, 1, 2, 2] ∧ LexLE [3, 1, 2, 2] [2, 2, 1, 3])) h)
                    · intro q
                      exact Fin.elim0 q
          · exact by
              constructor
              · exact by
                  intro _
                  exact k16t8_cover904
              · intro q
                fin_cases q
                · exact by
                    constructor
                    · exact by
                        intro h
                        exact False.elim ((by decide : ¬ (LexLE [] [3, 1, 3, 1] ∧ LexLE [3, 1, 3, 1] [1, 3, 1, 3])) h)
                    · intro q
                      exact Fin.elim0 q
          · exact by
              constructor
              · exact by
                  intro _
                  exact k16t8_cover905
              · intro q
                exact Fin.elim0 q
    · exact by
        constructor
        · exact by
            intro h
            exact False.elim ((by decide : ¬ (LexLE [] [3, 2] ∧ LexLE [3, 2] [2, 3])) h)
        · intro q
          fin_cases q
          · exact by
              constructor
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [] [3, 2, 1] ∧ LexLE [3, 2, 1] [1, 2, 3])) h)
              · intro q
                fin_cases q
                · exact by
                    constructor
                    · exact by
                        intro h
                        exact False.elim ((by decide : ¬ (LexLE [] [3, 2, 1, 1] ∧ LexLE [3, 2, 1, 1] [1, 1, 2, 3])) h)
                    · intro q
                      fin_cases q
                      · exact by
                          constructor
                          · exact by
                              intro h
                              exact False.elim ((by decide : ¬ (LexLE [] [3, 2, 1, 1, 1] ∧ LexLE [3, 2, 1, 1, 1] [1, 1, 1, 2, 3])) h)
                          · intro q
                            exact Fin.elim0 q
                · exact by
                    constructor
                    · exact by
                        intro h
                        exact False.elim ((by decide : ¬ (LexLE [] [3, 2, 1, 2] ∧ LexLE [3, 2, 1, 2] [2, 1, 2, 3])) h)
                    · intro q
                      exact Fin.elim0 q
          · exact by
              constructor
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [] [3, 2, 2] ∧ LexLE [3, 2, 2] [2, 2, 3])) h)
              · intro q
                fin_cases q
                · exact by
                    constructor
                    · exact by
                        intro h
                        exact False.elim ((by decide : ¬ (LexLE [] [3, 2, 2, 1] ∧ LexLE [3, 2, 2, 1] [1, 2, 2, 3])) h)
                    · intro q
                      exact Fin.elim0 q
          · exact by
              constructor
              · exact by
                  intro _
                  exact k16t8_cover906
              · intro q
                exact Fin.elim0 q
    · exact by
        constructor
        · exact by
            intro _
            exact k16t8_cover907
        · intro q
          fin_cases q
          · exact by
              constructor
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [] [3, 3, 1] ∧ LexLE [3, 3, 1] [1, 3, 3])) h)
              · intro q
                fin_cases q
                · exact by
                    constructor
                    · exact by
                        intro h
                        exact False.elim ((by decide : ¬ (LexLE [] [3, 3, 1, 1] ∧ LexLE [3, 3, 1, 1] [1, 1, 3, 3])) h)
                    · intro q
                      exact Fin.elim0 q
          · exact by
              constructor
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [] [3, 3, 2] ∧ LexLE [3, 3, 2] [2, 3, 3])) h)
              · intro q
                exact Fin.elim0 q
    · exact by
        constructor
        · exact by
            intro _
            exact k16t8_cover908
        · intro q
          fin_cases q
          · exact by
              constructor
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [] [3, 4, 1] ∧ LexLE [3, 4, 1] [1, 4, 3])) h)
              · intro q
                exact Fin.elim0 q
    · exact by
        constructor
        · exact by
            intro _
            exact k16t8_cover909
        · intro q
          exact Fin.elim0 q

private theorem k16t8_cover911 : ∀ P ∈ pathPatterns 3 0 [4], HasCheckedCertificate 16 8 ([[], [4], [4]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [4] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k16t8_cover910 : ∀ P ∈ pathPatterns 5 4 [4], HasCheckedCertificate 16 8 ([[], [4]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [4] [] ∧ LexLE [] [])) h)
      · intro q
        fin_cases q
        · exact by
            constructor
            · exact by
                intro h
                exact False.elim ((by decide : ¬ (LexLE [4] [1] ∧ LexLE [1] [1])) h)
            · intro q
              fin_cases q
              · exact by
                  constructor
                  · exact by
                      intro h
                      exact False.elim ((by decide : ¬ (LexLE [4] [1, 1] ∧ LexLE [1, 1] [1, 1])) h)
                  · intro q
                    fin_cases q
                    · exact by
                        constructor
                        · exact by
                            intro h
                            exact False.elim ((by decide : ¬ (LexLE [4] [1, 1, 1] ∧ LexLE [1, 1, 1] [1, 1, 1])) h)
                        · intro q
                          fin_cases q
                          · exact by
                              intro h
                              exact False.elim ((by decide : ¬ (LexLE [4] [1, 1, 1, 1] ∧ LexLE [1, 1, 1, 1] [1, 1, 1, 1])) h)
                    · exact by
                        constructor
                        · exact by
                            intro h
                            exact False.elim ((by decide : ¬ (LexLE [4] [1, 1, 2] ∧ LexLE [1, 1, 2] [2, 1, 1])) h)
                        · intro q
                          exact Fin.elim0 q
              · exact by
                  constructor
                  · exact by
                      intro h
                      exact False.elim ((by decide : ¬ (LexLE [4] [1, 2] ∧ LexLE [1, 2] [2, 1])) h)
                  · intro q
                    fin_cases q
                    · exact by
                        constructor
                        · exact by
                            intro h
                            exact False.elim ((by decide : ¬ (LexLE [4] [1, 2, 1] ∧ LexLE [1, 2, 1] [1, 2, 1])) h)
                        · intro q
                          exact Fin.elim0 q
              · exact by
                  constructor
                  · exact by
                      intro h
                      exact False.elim ((by decide : ¬ (LexLE [4] [1, 3] ∧ LexLE [1, 3] [3, 1])) h)
                  · intro q
                    exact Fin.elim0 q
        · exact by
            constructor
            · exact by
                intro h
                exact False.elim ((by decide : ¬ (LexLE [4] [2] ∧ LexLE [2] [2])) h)
            · intro q
              fin_cases q
              · exact by
                  constructor
                  · exact by
                      intro h
                      exact False.elim ((by decide : ¬ (LexLE [4] [2, 1] ∧ LexLE [2, 1] [1, 2])) h)
                  · intro q
                    fin_cases q
                    · exact by
                        constructor
                        · exact by
                            intro h
                            exact False.elim ((by decide : ¬ (LexLE [4] [2, 1, 1] ∧ LexLE [2, 1, 1] [1, 1, 2])) h)
                        · intro q
                          exact Fin.elim0 q
              · exact by
                  constructor
                  · exact by
                      intro h
                      exact False.elim ((by decide : ¬ (LexLE [4] [2, 2] ∧ LexLE [2, 2] [2, 2])) h)
                  · intro q
                    exact Fin.elim0 q
        · exact by
            constructor
            · exact by
                intro h
                exact False.elim ((by decide : ¬ (LexLE [4] [3] ∧ LexLE [3] [3])) h)
            · intro q
              fin_cases q
              · exact by
                  constructor
                  · exact by
                      intro h
                      exact False.elim ((by decide : ¬ (LexLE [4] [3, 1] ∧ LexLE [3, 1] [1, 3])) h)
                  · intro q
                    exact Fin.elim0 q
        · exact by
            constructor
            · exact by
                intro _
                exact k16t8_cover911
            · intro q
              exact Fin.elim0 q

private theorem k16t8_cover912 : ∀ P ∈ pathPatterns 4 0 [4, 4], HasCheckedCertificate 16 8 ([[], [4, 4]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [4, 4] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k16t8_cover913 : ∀ P ∈ pathPatterns 5 3 [5], HasCheckedCertificate 16 8 ([[], [5]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [5] [] ∧ LexLE [] [])) h)
      · intro q
        fin_cases q
        · exact by
            constructor
            · exact by
                intro h
                exact False.elim ((by decide : ¬ (LexLE [5] [1] ∧ LexLE [1] [1])) h)
            · intro q
              fin_cases q
              · exact by
                  constructor
                  · exact by
                      intro h
                      exact False.elim ((by decide : ¬ (LexLE [5] [1, 1] ∧ LexLE [1, 1] [1, 1])) h)
                  · intro q
                    fin_cases q
                    · exact by
                        constructor
                        · exact by
                            intro h
                            exact False.elim ((by decide : ¬ (LexLE [5] [1, 1, 1] ∧ LexLE [1, 1, 1] [1, 1, 1])) h)
                        · intro q
                          exact Fin.elim0 q
              · exact by
                  constructor
                  · exact by
                      intro h
                      exact False.elim ((by decide : ¬ (LexLE [5] [1, 2] ∧ LexLE [1, 2] [2, 1])) h)
                  · intro q
                    exact Fin.elim0 q
        · exact by
            constructor
            · exact by
                intro h
                exact False.elim ((by decide : ¬ (LexLE [5] [2] ∧ LexLE [2] [2])) h)
            · intro q
              fin_cases q
              · exact by
                  constructor
                  · exact by
                      intro h
                      exact False.elim ((by decide : ¬ (LexLE [5] [2, 1] ∧ LexLE [2, 1] [1, 2])) h)
                  · intro q
                    exact Fin.elim0 q
        · exact by
            constructor
            · exact by
                intro h
                exact False.elim ((by decide : ¬ (LexLE [5] [3] ∧ LexLE [3] [3])) h)
            · intro q
              exact Fin.elim0 q

private theorem k16t8_cover914 : ∀ P ∈ pathPatterns 5 2 [6], HasCheckedCertificate 16 8 ([[], [6]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [6] [] ∧ LexLE [] [])) h)
      · intro q
        fin_cases q
        · exact by
            constructor
            · exact by
                intro h
                exact False.elim ((by decide : ¬ (LexLE [6] [1] ∧ LexLE [1] [1])) h)
            · intro q
              fin_cases q
              · exact by
                  constructor
                  · exact by
                      intro h
                      exact False.elim ((by decide : ¬ (LexLE [6] [1, 1] ∧ LexLE [1, 1] [1, 1])) h)
                  · intro q
                    exact Fin.elim0 q
        · exact by
            constructor
            · exact by
                intro h
                exact False.elim ((by decide : ¬ (LexLE [6] [2] ∧ LexLE [2] [2])) h)
            · intro q
              exact Fin.elim0 q

private theorem k16t8_cover915 : ∀ P ∈ pathPatterns 5 1 [7], HasCheckedCertificate 16 8 ([[], [7]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [7] [] ∧ LexLE [] [])) h)
      · intro q
        fin_cases q
        · exact by
            constructor
            · exact by
                intro h
                exact False.elim ((by decide : ¬ (LexLE [7] [1] ∧ LexLE [1] [1])) h)
            · intro q
              exact Fin.elim0 q

private theorem k16t8_cover916 : ∀ P ∈ pathPatterns 5 0 [8], HasCheckedCertificate 16 8 ([[], [8]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [8] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k16t8_seq4 : amountSequenceForall 6 8 (fun tail =>
    (LexLE [] ([] ++ tail) ∧ LexLE ([] ++ tail) ([] ++ tail).reverse) →
    ∀ P ∈ pathPatterns (6 - ([] ++ tail).length) (8 - ([] ++ tail).sum) ([] ++ tail),
      HasCheckedCertificate 16 8 ([[]] ++ (([] ++ tail) :: P))) :=
by
  constructor
  · exact by
      intro _
      exact k16t8_cover5
  · intro q
    fin_cases q
    · exact k16t8_seq539

    · exact k16t8_seq841

    · exact k16t8_seq897

    · exact by
        constructor
        · exact by
            intro _
            exact k16t8_cover910
        · intro q
          fin_cases q
          · exact by
              constructor
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [] [4, 1] ∧ LexLE [4, 1] [1, 4])) h)
              · intro q
                fin_cases q
                · exact by
                    constructor
                    · exact by
                        intro h
                        exact False.elim ((by decide : ¬ (LexLE [] [4, 1, 1] ∧ LexLE [4, 1, 1] [1, 1, 4])) h)
                    · intro q
                      fin_cases q
                      · exact by
                          constructor
                          · exact by
                              intro h
                              exact False.elim ((by decide : ¬ (LexLE [] [4, 1, 1, 1] ∧ LexLE [4, 1, 1, 1] [1, 1, 1, 4])) h)
                          · intro q
                            fin_cases q
                            · exact by
                                constructor
                                · exact by
                                    intro h
                                    exact False.elim ((by decide : ¬ (LexLE [] [4, 1, 1, 1, 1] ∧ LexLE [4, 1, 1, 1, 1] [1, 1, 1, 1, 4])) h)
                                · intro q
                                  exact Fin.elim0 q
                      · exact by
                          constructor
                          · exact by
                              intro h
                              exact False.elim ((by decide : ¬ (LexLE [] [4, 1, 1, 2] ∧ LexLE [4, 1, 1, 2] [2, 1, 1, 4])) h)
                          · intro q
                            exact Fin.elim0 q
                · exact by
                    constructor
                    · exact by
                        intro h
                        exact False.elim ((by decide : ¬ (LexLE [] [4, 1, 2] ∧ LexLE [4, 1, 2] [2, 1, 4])) h)
                    · intro q
                      fin_cases q
                      · exact by
                          constructor
                          · exact by
                              intro h
                              exact False.elim ((by decide : ¬ (LexLE [] [4, 1, 2, 1] ∧ LexLE [4, 1, 2, 1] [1, 2, 1, 4])) h)
                          · intro q
                            exact Fin.elim0 q
                · exact by
                    constructor
                    · exact by
                        intro h
                        exact False.elim ((by decide : ¬ (LexLE [] [4, 1, 3] ∧ LexLE [4, 1, 3] [3, 1, 4])) h)
                    · intro q
                      exact Fin.elim0 q
          · exact by
              constructor
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [] [4, 2] ∧ LexLE [4, 2] [2, 4])) h)
              · intro q
                fin_cases q
                · exact by
                    constructor
                    · exact by
                        intro h
                        exact False.elim ((by decide : ¬ (LexLE [] [4, 2, 1] ∧ LexLE [4, 2, 1] [1, 2, 4])) h)
                    · intro q
                      fin_cases q
                      · exact by
                          constructor
                          · exact by
                              intro h
                              exact False.elim ((by decide : ¬ (LexLE [] [4, 2, 1, 1] ∧ LexLE [4, 2, 1, 1] [1, 1, 2, 4])) h)
                          · intro q
                            exact Fin.elim0 q
                · exact by
                    constructor
                    · exact by
                        intro h
                        exact False.elim ((by decide : ¬ (LexLE [] [4, 2, 2] ∧ LexLE [4, 2, 2] [2, 2, 4])) h)
                    · intro q
                      exact Fin.elim0 q
          · exact by
              constructor
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [] [4, 3] ∧ LexLE [4, 3] [3, 4])) h)
              · intro q
                fin_cases q
                · exact by
                    constructor
                    · exact by
                        intro h
                        exact False.elim ((by decide : ¬ (LexLE [] [4, 3, 1] ∧ LexLE [4, 3, 1] [1, 3, 4])) h)
                    · intro q
                      exact Fin.elim0 q
          · exact by
              constructor
              · exact by
                  intro _
                  exact k16t8_cover912
              · intro q
                exact Fin.elim0 q
    · exact by
        constructor
        · exact by
            intro _
            exact k16t8_cover913
        · intro q
          fin_cases q
          · exact by
              constructor
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [] [5, 1] ∧ LexLE [5, 1] [1, 5])) h)
              · intro q
                fin_cases q
                · exact by
                    constructor
                    · exact by
                        intro h
                        exact False.elim ((by decide : ¬ (LexLE [] [5, 1, 1] ∧ LexLE [5, 1, 1] [1, 1, 5])) h)
                    · intro q
                      fin_cases q
                      · exact by
                          constructor
                          · exact by
                              intro h
                              exact False.elim ((by decide : ¬ (LexLE [] [5, 1, 1, 1] ∧ LexLE [5, 1, 1, 1] [1, 1, 1, 5])) h)
                          · intro q
                            exact Fin.elim0 q
                · exact by
                    constructor
                    · exact by
                        intro h
                        exact False.elim ((by decide : ¬ (LexLE [] [5, 1, 2] ∧ LexLE [5, 1, 2] [2, 1, 5])) h)
                    · intro q
                      exact Fin.elim0 q
          · exact by
              constructor
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [] [5, 2] ∧ LexLE [5, 2] [2, 5])) h)
              · intro q
                fin_cases q
                · exact by
                    constructor
                    · exact by
                        intro h
                        exact False.elim ((by decide : ¬ (LexLE [] [5, 2, 1] ∧ LexLE [5, 2, 1] [1, 2, 5])) h)
                    · intro q
                      exact Fin.elim0 q
          · exact by
              constructor
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [] [5, 3] ∧ LexLE [5, 3] [3, 5])) h)
              · intro q
                exact Fin.elim0 q
    · exact by
        constructor
        · exact by
            intro _
            exact k16t8_cover914
        · intro q
          fin_cases q
          · exact by
              constructor
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [] [6, 1] ∧ LexLE [6, 1] [1, 6])) h)
              · intro q
                fin_cases q
                · exact by
                    constructor
                    · exact by
                        intro h
                        exact False.elim ((by decide : ¬ (LexLE [] [6, 1, 1] ∧ LexLE [6, 1, 1] [1, 1, 6])) h)
                    · intro q
                      exact Fin.elim0 q
          · exact by
              constructor
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [] [6, 2] ∧ LexLE [6, 2] [2, 6])) h)
              · intro q
                exact Fin.elim0 q
    · exact by
        constructor
        · exact by
            intro _
            exact k16t8_cover915
        · intro q
          fin_cases q
          · exact by
              constructor
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [] [7, 1] ∧ LexLE [7, 1] [1, 7])) h)
              · intro q
                exact Fin.elim0 q
    · exact by
        constructor
        · exact by
            intro _
            exact k16t8_cover916
        · intro q
          exact Fin.elim0 q

private theorem k16t8_cover3 : ∀ P ∈ pathPatterns 7 8 [], HasCheckedCertificate 16 8 ([[]] ++ P) := by
  apply pathPatterns_forall_step
  exact k16t8_seq4


private theorem k16t8_cover924 : ∀ P ∈ pathPatterns 0 4 [1], HasCheckedCertificate 16 8 ([[1], [1], [1], [1]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k16t8p364, Certificates.k16t8p364_check⟩

private theorem k16t8_cover925 : ∀ P ∈ pathPatterns 0 3 [2], HasCheckedCertificate 16 8 ([[1], [1], [1], [2]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k16t8p365, Certificates.k16t8p365_check⟩

private theorem k16t8_cover926 : ∀ P ∈ pathPatterns 0 2 [3], HasCheckedCertificate 16 8 ([[1], [1], [1], [3]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k16t8p366, Certificates.k16t8p366_check⟩

private theorem k16t8_cover927 : ∀ P ∈ pathPatterns 0 1 [4], HasCheckedCertificate 16 8 ([[1], [1], [1], [4]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k16t8p367, Certificates.k16t8p367_check⟩

private theorem k16t8_cover928 : ∀ P ∈ pathPatterns 0 0 [5], HasCheckedCertificate 16 8 ([[1], [1], [1], [5]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k16t8p368, Certificates.k16t8p368_check⟩

private theorem k16t8_cover923 : ∀ P ∈ pathPatterns 2 5 [1], HasCheckedCertificate 16 8 ([[1], [1], [1]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [1] [] ∧ LexLE [] [])) h)
      · intro q
        fin_cases q
        · exact by
            intro _
            exact k16t8_cover924
        · exact by
            intro _
            exact k16t8_cover925
        · exact by
            intro _
            exact k16t8_cover926
        · exact by
            intro _
            exact k16t8_cover927
        · exact by
            intro _
            exact k16t8_cover928

private theorem k16t8_cover929 : ∀ P ∈ pathPatterns 1 4 [1, 1], HasCheckedCertificate 16 8 ([[1], [1], [1, 1]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [1, 1] [] ∧ LexLE [] [])) h)

private theorem k16t8_cover930 : ∀ P ∈ pathPatterns 0 3 [1, 1, 1], HasCheckedCertificate 16 8 ([[1], [1], [1, 1, 1]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k16t8p369, Certificates.k16t8p369_check⟩

private theorem k16t8_cover931 : ∀ P ∈ pathPatterns 0 2 [1, 1, 2], HasCheckedCertificate 16 8 ([[1], [1], [1, 1, 2]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k16t8p370, Certificates.k16t8p370_check⟩

private theorem k16t8_cover932 : ∀ P ∈ pathPatterns 0 1 [1, 1, 3], HasCheckedCertificate 16 8 ([[1], [1], [1, 1, 3]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k16t8p371, Certificates.k16t8p371_check⟩

private theorem k16t8_cover933 : ∀ P ∈ pathPatterns 0 0 [1, 1, 4], HasCheckedCertificate 16 8 ([[1], [1], [1, 1, 4]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k16t8p372, Certificates.k16t8p372_check⟩

private theorem k16t8_cover934 : ∀ P ∈ pathPatterns 1 3 [1, 2], HasCheckedCertificate 16 8 ([[1], [1], [1, 2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [1, 2] [] ∧ LexLE [] [])) h)

private theorem k16t8_cover935 : ∀ P ∈ pathPatterns 0 2 [1, 2, 1], HasCheckedCertificate 16 8 ([[1], [1], [1, 2, 1]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k16t8p373, Certificates.k16t8p373_check⟩

private theorem k16t8_cover936 : ∀ P ∈ pathPatterns 0 1 [1, 2, 2], HasCheckedCertificate 16 8 ([[1], [1], [1, 2, 2]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k16t8p374, Certificates.k16t8p374_check⟩

private theorem k16t8_cover937 : ∀ P ∈ pathPatterns 0 0 [1, 2, 3], HasCheckedCertificate 16 8 ([[1], [1], [1, 2, 3]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k16t8p375, Certificates.k16t8p375_check⟩

private theorem k16t8_cover938 : ∀ P ∈ pathPatterns 1 2 [1, 3], HasCheckedCertificate 16 8 ([[1], [1], [1, 3]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [1, 3] [] ∧ LexLE [] [])) h)

private theorem k16t8_cover939 : ∀ P ∈ pathPatterns 0 1 [1, 3, 1], HasCheckedCertificate 16 8 ([[1], [1], [1, 3, 1]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k16t8p376, Certificates.k16t8p376_check⟩

private theorem k16t8_cover940 : ∀ P ∈ pathPatterns 0 0 [1, 3, 2], HasCheckedCertificate 16 8 ([[1], [1], [1, 3, 2]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k16t8p377, Certificates.k16t8p377_check⟩

private theorem k16t8_cover941 : ∀ P ∈ pathPatterns 1 1 [1, 4], HasCheckedCertificate 16 8 ([[1], [1], [1, 4]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [1, 4] [] ∧ LexLE [] [])) h)

private theorem k16t8_cover942 : ∀ P ∈ pathPatterns 0 0 [1, 4, 1], HasCheckedCertificate 16 8 ([[1], [1], [1, 4, 1]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k16t8p378, Certificates.k16t8p378_check⟩

private theorem k16t8_cover943 : ∀ P ∈ pathPatterns 1 0 [1, 5], HasCheckedCertificate 16 8 ([[1], [1], [1, 5]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [1, 5] [] ∧ LexLE [] [])) h)

private theorem k16t8_cover945 : ∀ P ∈ pathPatterns 0 2 [2], HasCheckedCertificate 16 8 ([[1], [1], [2], [2]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k16t8p379, Certificates.k16t8p379_check⟩

private theorem k16t8_cover946 : ∀ P ∈ pathPatterns 0 1 [3], HasCheckedCertificate 16 8 ([[1], [1], [2], [3]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k16t8p380, Certificates.k16t8p380_check⟩

private theorem k16t8_cover947 : ∀ P ∈ pathPatterns 0 0 [4], HasCheckedCertificate 16 8 ([[1], [1], [2], [4]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k16t8p381, Certificates.k16t8p381_check⟩

private theorem k16t8_cover944 : ∀ P ∈ pathPatterns 2 4 [2], HasCheckedCertificate 16 8 ([[1], [1], [2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [2] [] ∧ LexLE [] [])) h)
      · intro q
        fin_cases q
        · exact by
            intro h
            exact False.elim ((by decide : ¬ (LexLE [2] [1] ∧ LexLE [1] [1])) h)
        · exact by
            intro _
            exact k16t8_cover945
        · exact by
            intro _
            exact k16t8_cover946
        · exact by
            intro _
            exact k16t8_cover947

private theorem k16t8_cover948 : ∀ P ∈ pathPatterns 0 1 [2, 1, 2], HasCheckedCertificate 16 8 ([[1], [1], [2, 1, 2]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k16t8p382, Certificates.k16t8p382_check⟩

private theorem k16t8_cover949 : ∀ P ∈ pathPatterns 0 0 [2, 1, 3], HasCheckedCertificate 16 8 ([[1], [1], [2, 1, 3]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k16t8p383, Certificates.k16t8p383_check⟩

private theorem k16t8_cover950 : ∀ P ∈ pathPatterns 1 2 [2, 2], HasCheckedCertificate 16 8 ([[1], [1], [2, 2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [2, 2] [] ∧ LexLE [] [])) h)

private theorem k16t8_cover951 : ∀ P ∈ pathPatterns 0 0 [2, 2, 2], HasCheckedCertificate 16 8 ([[1], [1], [2, 2, 2]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k16t8p384, Certificates.k16t8p384_check⟩

private theorem k16t8_cover952 : ∀ P ∈ pathPatterns 1 1 [2, 3], HasCheckedCertificate 16 8 ([[1], [1], [2, 3]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [2, 3] [] ∧ LexLE [] [])) h)

private theorem k16t8_cover953 : ∀ P ∈ pathPatterns 1 0 [2, 4], HasCheckedCertificate 16 8 ([[1], [1], [2, 4]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [2, 4] [] ∧ LexLE [] [])) h)

private theorem k16t8_cover955 : ∀ P ∈ pathPatterns 0 0 [3], HasCheckedCertificate 16 8 ([[1], [1], [3], [3]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k16t8p385, Certificates.k16t8p385_check⟩

private theorem k16t8_cover954 : ∀ P ∈ pathPatterns 2 3 [3], HasCheckedCertificate 16 8 ([[1], [1], [3]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [3] [] ∧ LexLE [] [])) h)
      · intro q
        fin_cases q
        · exact by
            intro h
            exact False.elim ((by decide : ¬ (LexLE [3] [1] ∧ LexLE [1] [1])) h)
        · exact by
            intro h
            exact False.elim ((by decide : ¬ (LexLE [3] [2] ∧ LexLE [2] [2])) h)
        · exact by
            intro _
            exact k16t8_cover955

private theorem k16t8_cover956 : ∀ P ∈ pathPatterns 1 0 [3, 3], HasCheckedCertificate 16 8 ([[1], [1], [3, 3]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [3, 3] [] ∧ LexLE [] [])) h)

private theorem k16t8_cover957 : ∀ P ∈ pathPatterns 2 2 [4], HasCheckedCertificate 16 8 ([[1], [1], [4]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [4] [] ∧ LexLE [] [])) h)
      · intro q
        fin_cases q
        · exact by
            intro h
            exact False.elim ((by decide : ¬ (LexLE [4] [1] ∧ LexLE [1] [1])) h)
        · exact by
            intro h
            exact False.elim ((by decide : ¬ (LexLE [4] [2] ∧ LexLE [2] [2])) h)

private theorem k16t8_cover958 : ∀ P ∈ pathPatterns 2 1 [5], HasCheckedCertificate 16 8 ([[1], [1], [5]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [5] [] ∧ LexLE [] [])) h)
      · intro q
        fin_cases q
        · exact by
            intro h
            exact False.elim ((by decide : ¬ (LexLE [5] [1] ∧ LexLE [1] [1])) h)

private theorem k16t8_cover959 : ∀ P ∈ pathPatterns 2 0 [6], HasCheckedCertificate 16 8 ([[1], [1], [6]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [6] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k16t8_seq922 : amountSequenceForall 3 6 (fun tail =>
    (LexLE [1] ([] ++ tail) ∧ LexLE ([] ++ tail) ([] ++ tail).reverse) →
    ∀ P ∈ pathPatterns (3 - ([] ++ tail).length) (6 - ([] ++ tail).sum) ([] ++ tail),
      HasCheckedCertificate 16 8 ([[1], [1]] ++ (([] ++ tail) :: P))) :=
by
  constructor
  · exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [1] [] ∧ LexLE [] [])) h)
  · intro q
    fin_cases q
    · exact by
        constructor
        · exact by
            intro _
            exact k16t8_cover923
        · intro q
          fin_cases q
          · exact by
              constructor
              · exact by
                  intro _
                  exact k16t8_cover929
              · intro q
                fin_cases q
                · exact by
                    intro _
                    exact k16t8_cover930
                · exact by
                    intro _
                    exact k16t8_cover931
                · exact by
                    intro _
                    exact k16t8_cover932
                · exact by
                    intro _
                    exact k16t8_cover933
          · exact by
              constructor
              · exact by
                  intro _
                  exact k16t8_cover934
              · intro q
                fin_cases q
                · exact by
                    intro _
                    exact k16t8_cover935
                · exact by
                    intro _
                    exact k16t8_cover936
                · exact by
                    intro _
                    exact k16t8_cover937
          · exact by
              constructor
              · exact by
                  intro _
                  exact k16t8_cover938
              · intro q
                fin_cases q
                · exact by
                    intro _
                    exact k16t8_cover939
                · exact by
                    intro _
                    exact k16t8_cover940
          · exact by
              constructor
              · exact by
                  intro _
                  exact k16t8_cover941
              · intro q
                fin_cases q
                · exact by
                    intro _
                    exact k16t8_cover942
          · exact by
              constructor
              · exact by
                  intro _
                  exact k16t8_cover943
              · intro q
                exact Fin.elim0 q
    · exact by
        constructor
        · exact by
            intro _
            exact k16t8_cover944
        · intro q
          fin_cases q
          · exact by
              constructor
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [1] [2, 1] ∧ LexLE [2, 1] [1, 2])) h)
              · intro q
                fin_cases q
                · exact by
                    intro h
                    exact False.elim ((by decide : ¬ (LexLE [1] [2, 1, 1] ∧ LexLE [2, 1, 1] [1, 1, 2])) h)
                · exact by
                    intro _
                    exact k16t8_cover948
                · exact by
                    intro _
                    exact k16t8_cover949
          · exact by
              constructor
              · exact by
                  intro _
                  exact k16t8_cover950
              · intro q
                fin_cases q
                · exact by
                    intro h
                    exact False.elim ((by decide : ¬ (LexLE [1] [2, 2, 1] ∧ LexLE [2, 2, 1] [1, 2, 2])) h)
                · exact by
                    intro _
                    exact k16t8_cover951
          · exact by
              constructor
              · exact by
                  intro _
                  exact k16t8_cover952
              · intro q
                fin_cases q
                · exact by
                    intro h
                    exact False.elim ((by decide : ¬ (LexLE [1] [2, 3, 1] ∧ LexLE [2, 3, 1] [1, 3, 2])) h)
          · exact by
              constructor
              · exact by
                  intro _
                  exact k16t8_cover953
              · intro q
                exact Fin.elim0 q
    · exact by
        constructor
        · exact by
            intro _
            exact k16t8_cover954
        · intro q
          fin_cases q
          · exact by
              constructor
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [1] [3, 1] ∧ LexLE [3, 1] [1, 3])) h)
              · intro q
                fin_cases q
                · exact by
                    intro h
                    exact False.elim ((by decide : ¬ (LexLE [1] [3, 1, 1] ∧ LexLE [3, 1, 1] [1, 1, 3])) h)
                · exact by
                    intro h
                    exact False.elim ((by decide : ¬ (LexLE [1] [3, 1, 2] ∧ LexLE [3, 1, 2] [2, 1, 3])) h)
          · exact by
              constructor
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [1] [3, 2] ∧ LexLE [3, 2] [2, 3])) h)
              · intro q
                fin_cases q
                · exact by
                    intro h
                    exact False.elim ((by decide : ¬ (LexLE [1] [3, 2, 1] ∧ LexLE [3, 2, 1] [1, 2, 3])) h)
          · exact by
              constructor
              · exact by
                  intro _
                  exact k16t8_cover956
              · intro q
                exact Fin.elim0 q
    · exact by
        constructor
        · exact by
            intro _
            exact k16t8_cover957
        · intro q
          fin_cases q
          · exact by
              constructor
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [1] [4, 1] ∧ LexLE [4, 1] [1, 4])) h)
              · intro q
                fin_cases q
                · exact by
                    intro h
                    exact False.elim ((by decide : ¬ (LexLE [1] [4, 1, 1] ∧ LexLE [4, 1, 1] [1, 1, 4])) h)
          · exact by
              constructor
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [1] [4, 2] ∧ LexLE [4, 2] [2, 4])) h)
              · intro q
                exact Fin.elim0 q
    · exact by
        constructor
        · exact by
            intro _
            exact k16t8_cover958
        · intro q
          fin_cases q
          · exact by
              constructor
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [1] [5, 1] ∧ LexLE [5, 1] [1, 5])) h)
              · intro q
                exact Fin.elim0 q
    · exact by
        constructor
        · exact by
            intro _
            exact k16t8_cover959
        · intro q
          exact Fin.elim0 q

private theorem k16t8_cover921 : ∀ P ∈ pathPatterns 4 6 [1], HasCheckedCertificate 16 8 ([[1], [1]] ++ P) := by
  apply pathPatterns_forall_step
  exact k16t8_seq922


private theorem k16t8_cover962 : ∀ P ∈ pathPatterns 0 3 [1, 1], HasCheckedCertificate 16 8 ([[1], [1, 1], [1, 1]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k16t8p386, Certificates.k16t8p386_check⟩

private theorem k16t8_cover963 : ∀ P ∈ pathPatterns 0 2 [1, 2], HasCheckedCertificate 16 8 ([[1], [1, 1], [1, 2]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k16t8p387, Certificates.k16t8p387_check⟩

private theorem k16t8_cover964 : ∀ P ∈ pathPatterns 0 1 [1, 3], HasCheckedCertificate 16 8 ([[1], [1, 1], [1, 3]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k16t8p388, Certificates.k16t8p388_check⟩

private theorem k16t8_cover965 : ∀ P ∈ pathPatterns 0 0 [1, 4], HasCheckedCertificate 16 8 ([[1], [1, 1], [1, 4]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k16t8p389, Certificates.k16t8p389_check⟩

private theorem k16t8_cover966 : ∀ P ∈ pathPatterns 1 3 [2], HasCheckedCertificate 16 8 ([[1], [1, 1], [2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [2] [] ∧ LexLE [] [])) h)

private theorem k16t8_cover967 : ∀ P ∈ pathPatterns 0 1 [2, 2], HasCheckedCertificate 16 8 ([[1], [1, 1], [2, 2]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k16t8p390, Certificates.k16t8p390_check⟩

private theorem k16t8_cover968 : ∀ P ∈ pathPatterns 0 0 [2, 3], HasCheckedCertificate 16 8 ([[1], [1, 1], [2, 3]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k16t8p391, Certificates.k16t8p391_check⟩

private theorem k16t8_cover969 : ∀ P ∈ pathPatterns 1 2 [3], HasCheckedCertificate 16 8 ([[1], [1, 1], [3]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [3] [] ∧ LexLE [] [])) h)

private theorem k16t8_cover970 : ∀ P ∈ pathPatterns 1 1 [4], HasCheckedCertificate 16 8 ([[1], [1, 1], [4]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [4] [] ∧ LexLE [] [])) h)

private theorem k16t8_cover971 : ∀ P ∈ pathPatterns 1 0 [5], HasCheckedCertificate 16 8 ([[1], [1, 1], [5]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [5] [] ∧ LexLE [] [])) h)

private theorem k16t8_cover961 : ∀ P ∈ pathPatterns 3 5 [1, 1], HasCheckedCertificate 16 8 ([[1], [1, 1]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [1, 1] [] ∧ LexLE [] [])) h)
      · intro q
        fin_cases q
        · exact by
            constructor
            · exact by
                intro h
                exact False.elim ((by decide : ¬ (LexLE [1, 1] [1] ∧ LexLE [1] [1])) h)
            · intro q
              fin_cases q
              · exact by
                  intro _
                  exact k16t8_cover962
              · exact by
                  intro _
                  exact k16t8_cover963
              · exact by
                  intro _
                  exact k16t8_cover964
              · exact by
                  intro _
                  exact k16t8_cover965
        · exact by
            constructor
            · exact by
                intro _
                exact k16t8_cover966
            · intro q
              fin_cases q
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [1, 1] [2, 1] ∧ LexLE [2, 1] [1, 2])) h)
              · exact by
                  intro _
                  exact k16t8_cover967
              · exact by
                  intro _
                  exact k16t8_cover968
        · exact by
            constructor
            · exact by
                intro _
                exact k16t8_cover969
            · intro q
              fin_cases q
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [1, 1] [3, 1] ∧ LexLE [3, 1] [1, 3])) h)
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [1, 1] [3, 2] ∧ LexLE [3, 2] [2, 3])) h)
        · exact by
            constructor
            · exact by
                intro _
                exact k16t8_cover970
            · intro q
              fin_cases q
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [1, 1] [4, 1] ∧ LexLE [4, 1] [1, 4])) h)
        · exact by
            constructor
            · exact by
                intro _
                exact k16t8_cover971
            · intro q
              exact Fin.elim0 q

private theorem k16t8_cover973 : ∀ P ∈ pathPatterns 0 2 [2], HasCheckedCertificate 16 8 ([[1], [1, 1, 1], [2]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k16t8p392, Certificates.k16t8p392_check⟩

private theorem k16t8_cover974 : ∀ P ∈ pathPatterns 0 1 [3], HasCheckedCertificate 16 8 ([[1], [1, 1, 1], [3]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k16t8p393, Certificates.k16t8p393_check⟩

private theorem k16t8_cover975 : ∀ P ∈ pathPatterns 0 0 [4], HasCheckedCertificate 16 8 ([[1], [1, 1, 1], [4]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k16t8p394, Certificates.k16t8p394_check⟩

private theorem k16t8_cover972 : ∀ P ∈ pathPatterns 2 4 [1, 1, 1], HasCheckedCertificate 16 8 ([[1], [1, 1, 1]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [1, 1, 1] [] ∧ LexLE [] [])) h)
      · intro q
        fin_cases q
        · exact by
            intro h
            exact False.elim ((by decide : ¬ (LexLE [1, 1, 1] [1] ∧ LexLE [1] [1])) h)
        · exact by
            intro _
            exact k16t8_cover973
        · exact by
            intro _
            exact k16t8_cover974
        · exact by
            intro _
            exact k16t8_cover975

private theorem k16t8_cover976 : ∀ P ∈ pathPatterns 1 3 [1, 1, 1, 1], HasCheckedCertificate 16 8 ([[1], [1, 1, 1, 1]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [1, 1, 1, 1] [] ∧ LexLE [] [])) h)

private theorem k16t8_cover977 : ∀ P ∈ pathPatterns 0 2 [1, 1, 1, 1, 1], HasCheckedCertificate 16 8 ([[1], [1, 1, 1, 1, 1]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k16t8p395, Certificates.k16t8p395_check⟩

private theorem k16t8_cover978 : ∀ P ∈ pathPatterns 0 1 [1, 1, 1, 1, 2], HasCheckedCertificate 16 8 ([[1], [1, 1, 1, 1, 2]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k16t8p396, Certificates.k16t8p396_check⟩

private theorem k16t8_cover979 : ∀ P ∈ pathPatterns 0 0 [1, 1, 1, 1, 3], HasCheckedCertificate 16 8 ([[1], [1, 1, 1, 1, 3]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k16t8p397, Certificates.k16t8p397_check⟩

private theorem k16t8_cover980 : ∀ P ∈ pathPatterns 1 2 [1, 1, 1, 2], HasCheckedCertificate 16 8 ([[1], [1, 1, 1, 2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [1, 1, 1, 2] [] ∧ LexLE [] [])) h)

private theorem k16t8_cover981 : ∀ P ∈ pathPatterns 0 1 [1, 1, 1, 2, 1], HasCheckedCertificate 16 8 ([[1], [1, 1, 1, 2, 1]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k16t8p398, Certificates.k16t8p398_check⟩

private theorem k16t8_cover982 : ∀ P ∈ pathPatterns 0 0 [1, 1, 1, 2, 2], HasCheckedCertificate 16 8 ([[1], [1, 1, 1, 2, 2]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k16t8p399, Certificates.k16t8p399_check⟩

private theorem k16t8_cover983 : ∀ P ∈ pathPatterns 1 1 [1, 1, 1, 3], HasCheckedCertificate 16 8 ([[1], [1, 1, 1, 3]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [1, 1, 1, 3] [] ∧ LexLE [] [])) h)

private theorem k16t8_cover984 : ∀ P ∈ pathPatterns 0 0 [1, 1, 1, 3, 1], HasCheckedCertificate 16 8 ([[1], [1, 1, 1, 3, 1]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k16t8p400, Certificates.k16t8p400_check⟩

private theorem k16t8_cover985 : ∀ P ∈ pathPatterns 1 0 [1, 1, 1, 4], HasCheckedCertificate 16 8 ([[1], [1, 1, 1, 4]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [1, 1, 1, 4] [] ∧ LexLE [] [])) h)

private theorem k16t8_cover987 : ∀ P ∈ pathPatterns 0 1 [2], HasCheckedCertificate 16 8 ([[1], [1, 1, 2], [2]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k16t8p401, Certificates.k16t8p401_check⟩

private theorem k16t8_cover988 : ∀ P ∈ pathPatterns 0 0 [3], HasCheckedCertificate 16 8 ([[1], [1, 1, 2], [3]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k16t8p402, Certificates.k16t8p402_check⟩

private theorem k16t8_cover986 : ∀ P ∈ pathPatterns 2 3 [1, 1, 2], HasCheckedCertificate 16 8 ([[1], [1, 1, 2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [1, 1, 2] [] ∧ LexLE [] [])) h)
      · intro q
        fin_cases q
        · exact by
            intro h
            exact False.elim ((by decide : ¬ (LexLE [1, 1, 2] [1] ∧ LexLE [1] [1])) h)
        · exact by
            intro _
            exact k16t8_cover987
        · exact by
            intro _
            exact k16t8_cover988

private theorem k16t8_cover989 : ∀ P ∈ pathPatterns 1 2 [1, 1, 2, 1], HasCheckedCertificate 16 8 ([[1], [1, 1, 2, 1]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [1, 1, 2, 1] [] ∧ LexLE [] [])) h)

private theorem k16t8_cover990 : ∀ P ∈ pathPatterns 0 1 [1, 1, 2, 1, 1], HasCheckedCertificate 16 8 ([[1], [1, 1, 2, 1, 1]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k16t8p403, Certificates.k16t8p403_check⟩

private theorem k16t8_cover991 : ∀ P ∈ pathPatterns 0 0 [1, 1, 2, 1, 2], HasCheckedCertificate 16 8 ([[1], [1, 1, 2, 1, 2]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k16t8p404, Certificates.k16t8p404_check⟩

private theorem k16t8_cover992 : ∀ P ∈ pathPatterns 1 1 [1, 1, 2, 2], HasCheckedCertificate 16 8 ([[1], [1, 1, 2, 2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [1, 1, 2, 2] [] ∧ LexLE [] [])) h)

private theorem k16t8_cover993 : ∀ P ∈ pathPatterns 0 0 [1, 1, 2, 2, 1], HasCheckedCertificate 16 8 ([[1], [1, 1, 2, 2, 1]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k16t8p405, Certificates.k16t8p405_check⟩

private theorem k16t8_cover994 : ∀ P ∈ pathPatterns 1 0 [1, 1, 2, 3], HasCheckedCertificate 16 8 ([[1], [1, 1, 2, 3]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [1, 1, 2, 3] [] ∧ LexLE [] [])) h)

private theorem k16t8_cover996 : ∀ P ∈ pathPatterns 0 0 [2], HasCheckedCertificate 16 8 ([[1], [1, 1, 3], [2]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k16t8p406, Certificates.k16t8p406_check⟩

private theorem k16t8_cover995 : ∀ P ∈ pathPatterns 2 2 [1, 1, 3], HasCheckedCertificate 16 8 ([[1], [1, 1, 3]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [1, 1, 3] [] ∧ LexLE [] [])) h)
      · intro q
        fin_cases q
        · exact by
            intro h
            exact False.elim ((by decide : ¬ (LexLE [1, 1, 3] [1] ∧ LexLE [1] [1])) h)
        · exact by
            intro _
            exact k16t8_cover996

private theorem k16t8_cover997 : ∀ P ∈ pathPatterns 1 1 [1, 1, 3, 1], HasCheckedCertificate 16 8 ([[1], [1, 1, 3, 1]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [1, 1, 3, 1] [] ∧ LexLE [] [])) h)

private theorem k16t8_cover998 : ∀ P ∈ pathPatterns 0 0 [1, 1, 3, 1, 1], HasCheckedCertificate 16 8 ([[1], [1, 1, 3, 1, 1]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k16t8p407, Certificates.k16t8p407_check⟩

private theorem k16t8_cover999 : ∀ P ∈ pathPatterns 1 0 [1, 1, 3, 2], HasCheckedCertificate 16 8 ([[1], [1, 1, 3, 2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [1, 1, 3, 2] [] ∧ LexLE [] [])) h)

private theorem k16t8_cover1000 : ∀ P ∈ pathPatterns 2 1 [1, 1, 4], HasCheckedCertificate 16 8 ([[1], [1, 1, 4]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [1, 1, 4] [] ∧ LexLE [] [])) h)
      · intro q
        fin_cases q
        · exact by
            intro h
            exact False.elim ((by decide : ¬ (LexLE [1, 1, 4] [1] ∧ LexLE [1] [1])) h)

private theorem k16t8_cover1001 : ∀ P ∈ pathPatterns 1 0 [1, 1, 4, 1], HasCheckedCertificate 16 8 ([[1], [1, 1, 4, 1]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [1, 1, 4, 1] [] ∧ LexLE [] [])) h)

private theorem k16t8_cover1002 : ∀ P ∈ pathPatterns 2 0 [1, 1, 5], HasCheckedCertificate 16 8 ([[1], [1, 1, 5]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [1, 1, 5] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k16t8_seq960 : amountSequenceForall 3 5 (fun tail =>
    (LexLE [1] ([1, 1] ++ tail) ∧ LexLE ([1, 1] ++ tail) ([1, 1] ++ tail).reverse) →
    ∀ P ∈ pathPatterns (5 - ([1, 1] ++ tail).length) (7 - ([1, 1] ++ tail).sum) ([1, 1] ++ tail),
      HasCheckedCertificate 16 8 ([[1]] ++ (([1, 1] ++ tail) :: P))) :=
by
  constructor
  · exact by
      intro _
      exact k16t8_cover961
  · intro q
    fin_cases q
    · exact by
        constructor
        · exact by
            intro _
            exact k16t8_cover972
        · intro q
          fin_cases q
          · exact by
              constructor
              · exact by
                  intro _
                  exact k16t8_cover976
              · intro q
                fin_cases q
                · exact by
                    intro _
                    exact k16t8_cover977
                · exact by
                    intro _
                    exact k16t8_cover978
                · exact by
                    intro _
                    exact k16t8_cover979
          · exact by
              constructor
              · exact by
                  intro _
                  exact k16t8_cover980
              · intro q
                fin_cases q
                · exact by
                    intro _
                    exact k16t8_cover981
                · exact by
                    intro _
                    exact k16t8_cover982
          · exact by
              constructor
              · exact by
                  intro _
                  exact k16t8_cover983
              · intro q
                fin_cases q
                · exact by
                    intro _
                    exact k16t8_cover984
          · exact by
              constructor
              · exact by
                  intro _
                  exact k16t8_cover985
              · intro q
                exact Fin.elim0 q
    · exact by
        constructor
        · exact by
            intro _
            exact k16t8_cover986
        · intro q
          fin_cases q
          · exact by
              constructor
              · exact by
                  intro _
                  exact k16t8_cover989
              · intro q
                fin_cases q
                · exact by
                    intro _
                    exact k16t8_cover990
                · exact by
                    intro _
                    exact k16t8_cover991
          · exact by
              constructor
              · exact by
                  intro _
                  exact k16t8_cover992
              · intro q
                fin_cases q
                · exact by
                    intro _
                    exact k16t8_cover993
          · exact by
              constructor
              · exact by
                  intro _
                  exact k16t8_cover994
              · intro q
                exact Fin.elim0 q
    · exact by
        constructor
        · exact by
            intro _
            exact k16t8_cover995
        · intro q
          fin_cases q
          · exact by
              constructor
              · exact by
                  intro _
                  exact k16t8_cover997
              · intro q
                fin_cases q
                · exact by
                    intro _
                    exact k16t8_cover998
          · exact by
              constructor
              · exact by
                  intro _
                  exact k16t8_cover999
              · intro q
                exact Fin.elim0 q
    · exact by
        constructor
        · exact by
            intro _
            exact k16t8_cover1000
        · intro q
          fin_cases q
          · exact by
              constructor
              · exact by
                  intro _
                  exact k16t8_cover1001
              · intro q
                exact Fin.elim0 q
    · exact by
        constructor
        · exact by
            intro _
            exact k16t8_cover1002
        · intro q
          exact Fin.elim0 q

private theorem k16t8_cover1004 : ∀ P ∈ pathPatterns 0 1 [1, 2], HasCheckedCertificate 16 8 ([[1], [1, 2], [1, 2]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k16t8p408, Certificates.k16t8p408_check⟩

private theorem k16t8_cover1005 : ∀ P ∈ pathPatterns 0 0 [1, 3], HasCheckedCertificate 16 8 ([[1], [1, 2], [1, 3]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k16t8p409, Certificates.k16t8p409_check⟩

private theorem k16t8_cover1006 : ∀ P ∈ pathPatterns 1 2 [2], HasCheckedCertificate 16 8 ([[1], [1, 2], [2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [2] [] ∧ LexLE [] [])) h)

private theorem k16t8_cover1007 : ∀ P ∈ pathPatterns 0 0 [2, 2], HasCheckedCertificate 16 8 ([[1], [1, 2], [2, 2]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k16t8p410, Certificates.k16t8p410_check⟩

private theorem k16t8_cover1008 : ∀ P ∈ pathPatterns 1 1 [3], HasCheckedCertificate 16 8 ([[1], [1, 2], [3]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [3] [] ∧ LexLE [] [])) h)

private theorem k16t8_cover1009 : ∀ P ∈ pathPatterns 1 0 [4], HasCheckedCertificate 16 8 ([[1], [1, 2], [4]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [4] [] ∧ LexLE [] [])) h)

private theorem k16t8_cover1003 : ∀ P ∈ pathPatterns 3 4 [1, 2], HasCheckedCertificate 16 8 ([[1], [1, 2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [1, 2] [] ∧ LexLE [] [])) h)
      · intro q
        fin_cases q
        · exact by
            constructor
            · exact by
                intro h
                exact False.elim ((by decide : ¬ (LexLE [1, 2] [1] ∧ LexLE [1] [1])) h)
            · intro q
              fin_cases q
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [1, 2] [1, 1] ∧ LexLE [1, 1] [1, 1])) h)
              · exact by
                  intro _
                  exact k16t8_cover1004
              · exact by
                  intro _
                  exact k16t8_cover1005
        · exact by
            constructor
            · exact by
                intro _
                exact k16t8_cover1006
            · intro q
              fin_cases q
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [1, 2] [2, 1] ∧ LexLE [2, 1] [1, 2])) h)
              · exact by
                  intro _
                  exact k16t8_cover1007
        · exact by
            constructor
            · exact by
                intro _
                exact k16t8_cover1008
            · intro q
              fin_cases q
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [1, 2] [3, 1] ∧ LexLE [3, 1] [1, 3])) h)
        · exact by
            constructor
            · exact by
                intro _
                exact k16t8_cover1009
            · intro q
              exact Fin.elim0 q

private theorem k16t8_cover1011 : ∀ P ∈ pathPatterns 0 1 [2], HasCheckedCertificate 16 8 ([[1], [1, 2, 1], [2]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k16t8p411, Certificates.k16t8p411_check⟩

private theorem k16t8_cover1012 : ∀ P ∈ pathPatterns 0 0 [3], HasCheckedCertificate 16 8 ([[1], [1, 2, 1], [3]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k16t8p412, Certificates.k16t8p412_check⟩

private theorem k16t8_cover1010 : ∀ P ∈ pathPatterns 2 3 [1, 2, 1], HasCheckedCertificate 16 8 ([[1], [1, 2, 1]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [1, 2, 1] [] ∧ LexLE [] [])) h)
      · intro q
        fin_cases q
        · exact by
            intro h
            exact False.elim ((by decide : ¬ (LexLE [1, 2, 1] [1] ∧ LexLE [1] [1])) h)
        · exact by
            intro _
            exact k16t8_cover1011
        · exact by
            intro _
            exact k16t8_cover1012

private theorem k16t8_cover1013 : ∀ P ∈ pathPatterns 0 0 [1, 2, 1, 1, 2], HasCheckedCertificate 16 8 ([[1], [1, 2, 1, 1, 2]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k16t8p413, Certificates.k16t8p413_check⟩

private theorem k16t8_cover1014 : ∀ P ∈ pathPatterns 1 1 [1, 2, 1, 2], HasCheckedCertificate 16 8 ([[1], [1, 2, 1, 2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [1, 2, 1, 2] [] ∧ LexLE [] [])) h)

private theorem k16t8_cover1015 : ∀ P ∈ pathPatterns 0 0 [1, 2, 1, 2, 1], HasCheckedCertificate 16 8 ([[1], [1, 2, 1, 2, 1]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k16t8p414, Certificates.k16t8p414_check⟩

private theorem k16t8_cover1016 : ∀ P ∈ pathPatterns 1 0 [1, 2, 1, 3], HasCheckedCertificate 16 8 ([[1], [1, 2, 1, 3]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [1, 2, 1, 3] [] ∧ LexLE [] [])) h)

private theorem k16t8_cover1018 : ∀ P ∈ pathPatterns 0 0 [2], HasCheckedCertificate 16 8 ([[1], [1, 2, 2], [2]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k16t8p415, Certificates.k16t8p415_check⟩

private theorem k16t8_cover1017 : ∀ P ∈ pathPatterns 2 2 [1, 2, 2], HasCheckedCertificate 16 8 ([[1], [1, 2, 2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [1, 2, 2] [] ∧ LexLE [] [])) h)
      · intro q
        fin_cases q
        · exact by
            intro h
            exact False.elim ((by decide : ¬ (LexLE [1, 2, 2] [1] ∧ LexLE [1] [1])) h)
        · exact by
            intro _
            exact k16t8_cover1018

private theorem k16t8_cover1019 : ∀ P ∈ pathPatterns 1 1 [1, 2, 2, 1], HasCheckedCertificate 16 8 ([[1], [1, 2, 2, 1]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [1, 2, 2, 1] [] ∧ LexLE [] [])) h)

private theorem k16t8_cover1020 : ∀ P ∈ pathPatterns 1 0 [1, 2, 2, 2], HasCheckedCertificate 16 8 ([[1], [1, 2, 2, 2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [1, 2, 2, 2] [] ∧ LexLE [] [])) h)

private theorem k16t8_cover1021 : ∀ P ∈ pathPatterns 2 1 [1, 2, 3], HasCheckedCertificate 16 8 ([[1], [1, 2, 3]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [1, 2, 3] [] ∧ LexLE [] [])) h)
      · intro q
        fin_cases q
        · exact by
            intro h
            exact False.elim ((by decide : ¬ (LexLE [1, 2, 3] [1] ∧ LexLE [1] [1])) h)

private theorem k16t8_cover1022 : ∀ P ∈ pathPatterns 1 0 [1, 2, 3, 1], HasCheckedCertificate 16 8 ([[1], [1, 2, 3, 1]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [1, 2, 3, 1] [] ∧ LexLE [] [])) h)

private theorem k16t8_cover1023 : ∀ P ∈ pathPatterns 2 0 [1, 2, 4], HasCheckedCertificate 16 8 ([[1], [1, 2, 4]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [1, 2, 4] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k16t8_cover1025 : ∀ P ∈ pathPatterns 1 1 [2], HasCheckedCertificate 16 8 ([[1], [1, 3], [2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [2] [] ∧ LexLE [] [])) h)

private theorem k16t8_cover1026 : ∀ P ∈ pathPatterns 1 0 [3], HasCheckedCertificate 16 8 ([[1], [1, 3], [3]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [3] [] ∧ LexLE [] [])) h)

private theorem k16t8_cover1024 : ∀ P ∈ pathPatterns 3 3 [1, 3], HasCheckedCertificate 16 8 ([[1], [1, 3]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [1, 3] [] ∧ LexLE [] [])) h)
      · intro q
        fin_cases q
        · exact by
            constructor
            · exact by
                intro h
                exact False.elim ((by decide : ¬ (LexLE [1, 3] [1] ∧ LexLE [1] [1])) h)
            · intro q
              fin_cases q
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [1, 3] [1, 1] ∧ LexLE [1, 1] [1, 1])) h)
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [1, 3] [1, 2] ∧ LexLE [1, 2] [2, 1])) h)
        · exact by
            constructor
            · exact by
                intro _
                exact k16t8_cover1025
            · intro q
              fin_cases q
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [1, 3] [2, 1] ∧ LexLE [2, 1] [1, 2])) h)
        · exact by
            constructor
            · exact by
                intro _
                exact k16t8_cover1026
            · intro q
              exact Fin.elim0 q

private theorem k16t8_cover1028 : ∀ P ∈ pathPatterns 0 0 [2], HasCheckedCertificate 16 8 ([[1], [1, 3, 1], [2]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k16t8p416, Certificates.k16t8p416_check⟩

private theorem k16t8_cover1027 : ∀ P ∈ pathPatterns 2 2 [1, 3, 1], HasCheckedCertificate 16 8 ([[1], [1, 3, 1]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [1, 3, 1] [] ∧ LexLE [] [])) h)
      · intro q
        fin_cases q
        · exact by
            intro h
            exact False.elim ((by decide : ¬ (LexLE [1, 3, 1] [1] ∧ LexLE [1] [1])) h)
        · exact by
            intro _
            exact k16t8_cover1028

private theorem k16t8_cover1029 : ∀ P ∈ pathPatterns 1 0 [1, 3, 1, 2], HasCheckedCertificate 16 8 ([[1], [1, 3, 1, 2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [1, 3, 1, 2] [] ∧ LexLE [] [])) h)

private theorem k16t8_cover1030 : ∀ P ∈ pathPatterns 2 1 [1, 3, 2], HasCheckedCertificate 16 8 ([[1], [1, 3, 2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [1, 3, 2] [] ∧ LexLE [] [])) h)
      · intro q
        fin_cases q
        · exact by
            intro h
            exact False.elim ((by decide : ¬ (LexLE [1, 3, 2] [1] ∧ LexLE [1] [1])) h)

private theorem k16t8_cover1031 : ∀ P ∈ pathPatterns 2 0 [1, 3, 3], HasCheckedCertificate 16 8 ([[1], [1, 3, 3]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [1, 3, 3] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k16t8_cover1033 : ∀ P ∈ pathPatterns 1 0 [2], HasCheckedCertificate 16 8 ([[1], [1, 4], [2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [2] [] ∧ LexLE [] [])) h)

private theorem k16t8_cover1032 : ∀ P ∈ pathPatterns 3 2 [1, 4], HasCheckedCertificate 16 8 ([[1], [1, 4]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [1, 4] [] ∧ LexLE [] [])) h)
      · intro q
        fin_cases q
        · exact by
            constructor
            · exact by
                intro h
                exact False.elim ((by decide : ¬ (LexLE [1, 4] [1] ∧ LexLE [1] [1])) h)
            · intro q
              fin_cases q
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [1, 4] [1, 1] ∧ LexLE [1, 1] [1, 1])) h)
        · exact by
            constructor
            · exact by
                intro _
                exact k16t8_cover1033
            · intro q
              exact Fin.elim0 q

private theorem k16t8_cover1034 : ∀ P ∈ pathPatterns 2 1 [1, 4, 1], HasCheckedCertificate 16 8 ([[1], [1, 4, 1]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [1, 4, 1] [] ∧ LexLE [] [])) h)
      · intro q
        fin_cases q
        · exact by
            intro h
            exact False.elim ((by decide : ¬ (LexLE [1, 4, 1] [1] ∧ LexLE [1] [1])) h)

private theorem k16t8_cover1035 : ∀ P ∈ pathPatterns 2 0 [1, 4, 2], HasCheckedCertificate 16 8 ([[1], [1, 4, 2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [1, 4, 2] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k16t8_cover1036 : ∀ P ∈ pathPatterns 3 1 [1, 5], HasCheckedCertificate 16 8 ([[1], [1, 5]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [1, 5] [] ∧ LexLE [] [])) h)
      · intro q
        fin_cases q
        · exact by
            constructor
            · exact by
                intro h
                exact False.elim ((by decide : ¬ (LexLE [1, 5] [1] ∧ LexLE [1] [1])) h)
            · intro q
              exact Fin.elim0 q

private theorem k16t8_cover1037 : ∀ P ∈ pathPatterns 2 0 [1, 5, 1], HasCheckedCertificate 16 8 ([[1], [1, 5, 1]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [1, 5, 1] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k16t8_cover1038 : ∀ P ∈ pathPatterns 3 0 [1, 6], HasCheckedCertificate 16 8 ([[1], [1, 6]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [1, 6] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k16t8_seq920 : amountSequenceForall 4 6 (fun tail =>
    (LexLE [1] ([1] ++ tail) ∧ LexLE ([1] ++ tail) ([1] ++ tail).reverse) →
    ∀ P ∈ pathPatterns (5 - ([1] ++ tail).length) (7 - ([1] ++ tail).sum) ([1] ++ tail),
      HasCheckedCertificate 16 8 ([[1]] ++ (([1] ++ tail) :: P))) :=
by
  constructor
  · exact by
      intro _
      exact k16t8_cover921
  · intro q
    fin_cases q
    · exact k16t8_seq960

    · exact by
        constructor
        · exact by
            intro _
            exact k16t8_cover1003
        · intro q
          fin_cases q
          · exact by
              constructor
              · exact by
                  intro _
                  exact k16t8_cover1010
              · intro q
                fin_cases q
                · exact by
                    constructor
                    · exact by
                        intro h
                        exact False.elim ((by decide : ¬ (LexLE [1] [1, 2, 1, 1] ∧ LexLE [1, 2, 1, 1] [1, 1, 2, 1])) h)
                    · intro q
                      fin_cases q
                      · exact by
                          intro h
                          exact False.elim ((by decide : ¬ (LexLE [1] [1, 2, 1, 1, 1] ∧ LexLE [1, 2, 1, 1, 1] [1, 1, 1, 2, 1])) h)
                      · exact by
                          intro _
                          exact k16t8_cover1013
                · exact by
                    constructor
                    · exact by
                        intro _
                        exact k16t8_cover1014
                    · intro q
                      fin_cases q
                      · exact by
                          intro _
                          exact k16t8_cover1015
                · exact by
                    constructor
                    · exact by
                        intro _
                        exact k16t8_cover1016
                    · intro q
                      exact Fin.elim0 q
          · exact by
              constructor
              · exact by
                  intro _
                  exact k16t8_cover1017
              · intro q
                fin_cases q
                · exact by
                    constructor
                    · exact by
                        intro _
                        exact k16t8_cover1019
                    · intro q
                      fin_cases q
                      · exact by
                          intro h
                          exact False.elim ((by decide : ¬ (LexLE [1] [1, 2, 2, 1, 1] ∧ LexLE [1, 2, 2, 1, 1] [1, 1, 2, 2, 1])) h)
                · exact by
                    constructor
                    · exact by
                        intro _
                        exact k16t8_cover1020
                    · intro q
                      exact Fin.elim0 q
          · exact by
              constructor
              · exact by
                  intro _
                  exact k16t8_cover1021
              · intro q
                fin_cases q
                · exact by
                    constructor
                    · exact by
                        intro _
                        exact k16t8_cover1022
                    · intro q
                      exact Fin.elim0 q
          · exact by
              constructor
              · exact by
                  intro _
                  exact k16t8_cover1023
              · intro q
                exact Fin.elim0 q
    · exact by
        constructor
        · exact by
            intro _
            exact k16t8_cover1024
        · intro q
          fin_cases q
          · exact by
              constructor
              · exact by
                  intro _
                  exact k16t8_cover1027
              · intro q
                fin_cases q
                · exact by
                    constructor
                    · exact by
                        intro h
                        exact False.elim ((by decide : ¬ (LexLE [1] [1, 3, 1, 1] ∧ LexLE [1, 3, 1, 1] [1, 1, 3, 1])) h)
                    · intro q
                      fin_cases q
                      · exact by
                          intro h
                          exact False.elim ((by decide : ¬ (LexLE [1] [1, 3, 1, 1, 1] ∧ LexLE [1, 3, 1, 1, 1] [1, 1, 1, 3, 1])) h)
                · exact by
                    constructor
                    · exact by
                        intro _
                        exact k16t8_cover1029
                    · intro q
                      exact Fin.elim0 q
          · exact by
              constructor
              · exact by
                  intro _
                  exact k16t8_cover1030
              · intro q
                fin_cases q
                · exact by
                    constructor
                    · exact by
                        intro h
                        exact False.elim ((by decide : ¬ (LexLE [1] [1, 3, 2, 1] ∧ LexLE [1, 3, 2, 1] [1, 2, 3, 1])) h)
                    · intro q
                      exact Fin.elim0 q
          · exact by
              constructor
              · exact by
                  intro _
                  exact k16t8_cover1031
              · intro q
                exact Fin.elim0 q
    · exact by
        constructor
        · exact by
            intro _
            exact k16t8_cover1032
        · intro q
          fin_cases q
          · exact by
              constructor
              · exact by
                  intro _
                  exact k16t8_cover1034
              · intro q
                fin_cases q
                · exact by
                    constructor
                    · exact by
                        intro h
                        exact False.elim ((by decide : ¬ (LexLE [1] [1, 4, 1, 1] ∧ LexLE [1, 4, 1, 1] [1, 1, 4, 1])) h)
                    · intro q
                      exact Fin.elim0 q
          · exact by
              constructor
              · exact by
                  intro _
                  exact k16t8_cover1035
              · intro q
                exact Fin.elim0 q
    · exact by
        constructor
        · exact by
            intro _
            exact k16t8_cover1036
        · intro q
          fin_cases q
          · exact by
              constructor
              · exact by
                  intro _
                  exact k16t8_cover1037
              · intro q
                exact Fin.elim0 q
    · exact by
        constructor
        · exact by
            intro _
            exact k16t8_cover1038
        · intro q
          exact Fin.elim0 q

private theorem k16t8_cover1043 : ∀ P ∈ pathPatterns 0 1 [2], HasCheckedCertificate 16 8 ([[1], [2], [2], [2]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k16t8p417, Certificates.k16t8p417_check⟩

private theorem k16t8_cover1044 : ∀ P ∈ pathPatterns 0 0 [3], HasCheckedCertificate 16 8 ([[1], [2], [2], [3]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k16t8p418, Certificates.k16t8p418_check⟩

private theorem k16t8_cover1042 : ∀ P ∈ pathPatterns 2 3 [2], HasCheckedCertificate 16 8 ([[1], [2], [2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [2] [] ∧ LexLE [] [])) h)
      · intro q
        fin_cases q
        · exact by
            intro h
            exact False.elim ((by decide : ¬ (LexLE [2] [1] ∧ LexLE [1] [1])) h)
        · exact by
            intro _
            exact k16t8_cover1043
        · exact by
            intro _
            exact k16t8_cover1044

private theorem k16t8_cover1045 : ∀ P ∈ pathPatterns 0 0 [2, 1, 2], HasCheckedCertificate 16 8 ([[1], [2], [2, 1, 2]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k16t8p419, Certificates.k16t8p419_check⟩

private theorem k16t8_cover1046 : ∀ P ∈ pathPatterns 1 1 [2, 2], HasCheckedCertificate 16 8 ([[1], [2], [2, 2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [2, 2] [] ∧ LexLE [] [])) h)

private theorem k16t8_cover1047 : ∀ P ∈ pathPatterns 1 0 [2, 3], HasCheckedCertificate 16 8 ([[1], [2], [2, 3]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [2, 3] [] ∧ LexLE [] [])) h)

private theorem k16t8_cover1048 : ∀ P ∈ pathPatterns 2 2 [3], HasCheckedCertificate 16 8 ([[1], [2], [3]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [3] [] ∧ LexLE [] [])) h)
      · intro q
        fin_cases q
        · exact by
            intro h
            exact False.elim ((by decide : ¬ (LexLE [3] [1] ∧ LexLE [1] [1])) h)
        · exact by
            intro h
            exact False.elim ((by decide : ¬ (LexLE [3] [2] ∧ LexLE [2] [2])) h)

private theorem k16t8_cover1049 : ∀ P ∈ pathPatterns 2 1 [4], HasCheckedCertificate 16 8 ([[1], [2], [4]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [4] [] ∧ LexLE [] [])) h)
      · intro q
        fin_cases q
        · exact by
            intro h
            exact False.elim ((by decide : ¬ (LexLE [4] [1] ∧ LexLE [1] [1])) h)

private theorem k16t8_cover1050 : ∀ P ∈ pathPatterns 2 0 [5], HasCheckedCertificate 16 8 ([[1], [2], [5]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [5] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k16t8_seq1041 : amountSequenceForall 3 5 (fun tail =>
    (LexLE [2] ([] ++ tail) ∧ LexLE ([] ++ tail) ([] ++ tail).reverse) →
    ∀ P ∈ pathPatterns (3 - ([] ++ tail).length) (5 - ([] ++ tail).sum) ([] ++ tail),
      HasCheckedCertificate 16 8 ([[1], [2]] ++ (([] ++ tail) :: P))) :=
by
  constructor
  · exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [2] [] ∧ LexLE [] [])) h)
  · intro q
    fin_cases q
    · exact by
        constructor
        · exact by
            intro h
            exact False.elim ((by decide : ¬ (LexLE [2] [1] ∧ LexLE [1] [1])) h)
        · intro q
          fin_cases q
          · exact by
              constructor
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [2] [1, 1] ∧ LexLE [1, 1] [1, 1])) h)
              · intro q
                fin_cases q
                · exact by
                    intro h
                    exact False.elim ((by decide : ¬ (LexLE [2] [1, 1, 1] ∧ LexLE [1, 1, 1] [1, 1, 1])) h)
                · exact by
                    intro h
                    exact False.elim ((by decide : ¬ (LexLE [2] [1, 1, 2] ∧ LexLE [1, 1, 2] [2, 1, 1])) h)
                · exact by
                    intro h
                    exact False.elim ((by decide : ¬ (LexLE [2] [1, 1, 3] ∧ LexLE [1, 1, 3] [3, 1, 1])) h)
          · exact by
              constructor
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [2] [1, 2] ∧ LexLE [1, 2] [2, 1])) h)
              · intro q
                fin_cases q
                · exact by
                    intro h
                    exact False.elim ((by decide : ¬ (LexLE [2] [1, 2, 1] ∧ LexLE [1, 2, 1] [1, 2, 1])) h)
                · exact by
                    intro h
                    exact False.elim ((by decide : ¬ (LexLE [2] [1, 2, 2] ∧ LexLE [1, 2, 2] [2, 2, 1])) h)
          · exact by
              constructor
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [2] [1, 3] ∧ LexLE [1, 3] [3, 1])) h)
              · intro q
                fin_cases q
                · exact by
                    intro h
                    exact False.elim ((by decide : ¬ (LexLE [2] [1, 3, 1] ∧ LexLE [1, 3, 1] [1, 3, 1])) h)
          · exact by
              constructor
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [2] [1, 4] ∧ LexLE [1, 4] [4, 1])) h)
              · intro q
                exact Fin.elim0 q
    · exact by
        constructor
        · exact by
            intro _
            exact k16t8_cover1042
        · intro q
          fin_cases q
          · exact by
              constructor
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [2] [2, 1] ∧ LexLE [2, 1] [1, 2])) h)
              · intro q
                fin_cases q
                · exact by
                    intro h
                    exact False.elim ((by decide : ¬ (LexLE [2] [2, 1, 1] ∧ LexLE [2, 1, 1] [1, 1, 2])) h)
                · exact by
                    intro _
                    exact k16t8_cover1045
          · exact by
              constructor
              · exact by
                  intro _
                  exact k16t8_cover1046
              · intro q
                fin_cases q
                · exact by
                    intro h
                    exact False.elim ((by decide : ¬ (LexLE [2] [2, 2, 1] ∧ LexLE [2, 2, 1] [1, 2, 2])) h)
          · exact by
              constructor
              · exact by
                  intro _
                  exact k16t8_cover1047
              · intro q
                exact Fin.elim0 q
    · exact by
        constructor
        · exact by
            intro _
            exact k16t8_cover1048
        · intro q
          fin_cases q
          · exact by
              constructor
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [2] [3, 1] ∧ LexLE [3, 1] [1, 3])) h)
              · intro q
                fin_cases q
                · exact by
                    intro h
                    exact False.elim ((by decide : ¬ (LexLE [2] [3, 1, 1] ∧ LexLE [3, 1, 1] [1, 1, 3])) h)
          · exact by
              constructor
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [2] [3, 2] ∧ LexLE [3, 2] [2, 3])) h)
              · intro q
                exact Fin.elim0 q
    · exact by
        constructor
        · exact by
            intro _
            exact k16t8_cover1049
        · intro q
          fin_cases q
          · exact by
              constructor
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [2] [4, 1] ∧ LexLE [4, 1] [1, 4])) h)
              · intro q
                exact Fin.elim0 q
    · exact by
        constructor
        · exact by
            intro _
            exact k16t8_cover1050
        · intro q
          exact Fin.elim0 q

private theorem k16t8_cover1040 : ∀ P ∈ pathPatterns 4 5 [2], HasCheckedCertificate 16 8 ([[1], [2]] ++ P) := by
  apply pathPatterns_forall_step
  exact k16t8_seq1041


private theorem k16t8_cover1051 : ∀ P ∈ pathPatterns 0 0 [2, 1, 1, 1, 2], HasCheckedCertificate 16 8 ([[1], [2, 1, 1, 1, 2]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k16t8p420, Certificates.k16t8p420_check⟩

private theorem k16t8_cover1052 : ∀ P ∈ pathPatterns 1 1 [2, 1, 1, 2], HasCheckedCertificate 16 8 ([[1], [2, 1, 1, 2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [2, 1, 1, 2] [] ∧ LexLE [] [])) h)

private theorem k16t8_cover1053 : ∀ P ∈ pathPatterns 1 0 [2, 1, 1, 3], HasCheckedCertificate 16 8 ([[1], [2, 1, 1, 3]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [2, 1, 1, 3] [] ∧ LexLE [] [])) h)

private theorem k16t8_cover1054 : ∀ P ∈ pathPatterns 2 2 [2, 1, 2], HasCheckedCertificate 16 8 ([[1], [2, 1, 2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [2, 1, 2] [] ∧ LexLE [] [])) h)
      · intro q
        fin_cases q
        · exact by
            intro h
            exact False.elim ((by decide : ¬ (LexLE [2, 1, 2] [1] ∧ LexLE [1] [1])) h)
        · exact by
            intro h
            exact False.elim ((by decide : ¬ (LexLE [2, 1, 2] [2] ∧ LexLE [2] [2])) h)

private theorem k16t8_cover1055 : ∀ P ∈ pathPatterns 1 0 [2, 1, 2, 2], HasCheckedCertificate 16 8 ([[1], [2, 1, 2, 2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [2, 1, 2, 2] [] ∧ LexLE [] [])) h)

private theorem k16t8_cover1056 : ∀ P ∈ pathPatterns 2 1 [2, 1, 3], HasCheckedCertificate 16 8 ([[1], [2, 1, 3]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [2, 1, 3] [] ∧ LexLE [] [])) h)
      · intro q
        fin_cases q
        · exact by
            intro h
            exact False.elim ((by decide : ¬ (LexLE [2, 1, 3] [1] ∧ LexLE [1] [1])) h)

private theorem k16t8_cover1057 : ∀ P ∈ pathPatterns 2 0 [2, 1, 4], HasCheckedCertificate 16 8 ([[1], [2, 1, 4]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [2, 1, 4] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k16t8_cover1059 : ∀ P ∈ pathPatterns 1 0 [3], HasCheckedCertificate 16 8 ([[1], [2, 2], [3]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [3] [] ∧ LexLE [] [])) h)

private theorem k16t8_cover1058 : ∀ P ∈ pathPatterns 3 3 [2, 2], HasCheckedCertificate 16 8 ([[1], [2, 2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [2, 2] [] ∧ LexLE [] [])) h)
      · intro q
        fin_cases q
        · exact by
            constructor
            · exact by
                intro h
                exact False.elim ((by decide : ¬ (LexLE [2, 2] [1] ∧ LexLE [1] [1])) h)
            · intro q
              fin_cases q
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [2, 2] [1, 1] ∧ LexLE [1, 1] [1, 1])) h)
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [2, 2] [1, 2] ∧ LexLE [1, 2] [2, 1])) h)
        · exact by
            constructor
            · exact by
                intro h
                exact False.elim ((by decide : ¬ (LexLE [2, 2] [2] ∧ LexLE [2] [2])) h)
            · intro q
              fin_cases q
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [2, 2] [2, 1] ∧ LexLE [2, 1] [1, 2])) h)
        · exact by
            constructor
            · exact by
                intro _
                exact k16t8_cover1059
            · intro q
              exact Fin.elim0 q

private theorem k16t8_cover1060 : ∀ P ∈ pathPatterns 2 1 [2, 2, 2], HasCheckedCertificate 16 8 ([[1], [2, 2, 2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [2, 2, 2] [] ∧ LexLE [] [])) h)
      · intro q
        fin_cases q
        · exact by
            intro h
            exact False.elim ((by decide : ¬ (LexLE [2, 2, 2] [1] ∧ LexLE [1] [1])) h)

private theorem k16t8_cover1061 : ∀ P ∈ pathPatterns 2 0 [2, 2, 3], HasCheckedCertificate 16 8 ([[1], [2, 2, 3]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [2, 2, 3] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k16t8_cover1062 : ∀ P ∈ pathPatterns 3 2 [2, 3], HasCheckedCertificate 16 8 ([[1], [2, 3]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [2, 3] [] ∧ LexLE [] [])) h)
      · intro q
        fin_cases q
        · exact by
            constructor
            · exact by
                intro h
                exact False.elim ((by decide : ¬ (LexLE [2, 3] [1] ∧ LexLE [1] [1])) h)
            · intro q
              fin_cases q
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [2, 3] [1, 1] ∧ LexLE [1, 1] [1, 1])) h)
        · exact by
            constructor
            · exact by
                intro h
                exact False.elim ((by decide : ¬ (LexLE [2, 3] [2] ∧ LexLE [2] [2])) h)
            · intro q
              exact Fin.elim0 q

private theorem k16t8_cover1063 : ∀ P ∈ pathPatterns 2 0 [2, 3, 2], HasCheckedCertificate 16 8 ([[1], [2, 3, 2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [2, 3, 2] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k16t8_cover1064 : ∀ P ∈ pathPatterns 3 1 [2, 4], HasCheckedCertificate 16 8 ([[1], [2, 4]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [2, 4] [] ∧ LexLE [] [])) h)
      · intro q
        fin_cases q
        · exact by
            constructor
            · exact by
                intro h
                exact False.elim ((by decide : ¬ (LexLE [2, 4] [1] ∧ LexLE [1] [1])) h)
            · intro q
              exact Fin.elim0 q

private theorem k16t8_cover1065 : ∀ P ∈ pathPatterns 3 0 [2, 5], HasCheckedCertificate 16 8 ([[1], [2, 5]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [2, 5] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k16t8_seq1039 : amountSequenceForall 4 5 (fun tail =>
    (LexLE [1] ([2] ++ tail) ∧ LexLE ([2] ++ tail) ([2] ++ tail).reverse) →
    ∀ P ∈ pathPatterns (5 - ([2] ++ tail).length) (7 - ([2] ++ tail).sum) ([2] ++ tail),
      HasCheckedCertificate 16 8 ([[1]] ++ (([2] ++ tail) :: P))) :=
by
  constructor
  · exact by
      intro _
      exact k16t8_cover1040
  · intro q
    fin_cases q
    · exact by
        constructor
        · exact by
            intro h
            exact False.elim ((by decide : ¬ (LexLE [1] [2, 1] ∧ LexLE [2, 1] [1, 2])) h)
        · intro q
          fin_cases q
          · exact by
              constructor
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [1] [2, 1, 1] ∧ LexLE [2, 1, 1] [1, 1, 2])) h)
              · intro q
                fin_cases q
                · exact by
                    constructor
                    · exact by
                        intro h
                        exact False.elim ((by decide : ¬ (LexLE [1] [2, 1, 1, 1] ∧ LexLE [2, 1, 1, 1] [1, 1, 1, 2])) h)
                    · intro q
                      fin_cases q
                      · exact by
                          intro h
                          exact False.elim ((by decide : ¬ (LexLE [1] [2, 1, 1, 1, 1] ∧ LexLE [2, 1, 1, 1, 1] [1, 1, 1, 1, 2])) h)
                      · exact by
                          intro _
                          exact k16t8_cover1051
                · exact by
                    constructor
                    · exact by
                        intro _
                        exact k16t8_cover1052
                    · intro q
                      fin_cases q
                      · exact by
                          intro h
                          exact False.elim ((by decide : ¬ (LexLE [1] [2, 1, 1, 2, 1] ∧ LexLE [2, 1, 1, 2, 1] [1, 2, 1, 1, 2])) h)
                · exact by
                    constructor
                    · exact by
                        intro _
                        exact k16t8_cover1053
                    · intro q
                      exact Fin.elim0 q
          · exact by
              constructor
              · exact by
                  intro _
                  exact k16t8_cover1054
              · intro q
                fin_cases q
                · exact by
                    constructor
                    · exact by
                        intro h
                        exact False.elim ((by decide : ¬ (LexLE [1] [2, 1, 2, 1] ∧ LexLE [2, 1, 2, 1] [1, 2, 1, 2])) h)
                    · intro q
                      fin_cases q
                      · exact by
                          intro h
                          exact False.elim ((by decide : ¬ (LexLE [1] [2, 1, 2, 1, 1] ∧ LexLE [2, 1, 2, 1, 1] [1, 1, 2, 1, 2])) h)
                · exact by
                    constructor
                    · exact by
                        intro _
                        exact k16t8_cover1055
                    · intro q
                      exact Fin.elim0 q
          · exact by
              constructor
              · exact by
                  intro _
                  exact k16t8_cover1056
              · intro q
                fin_cases q
                · exact by
                    constructor
                    · exact by
                        intro h
                        exact False.elim ((by decide : ¬ (LexLE [1] [2, 1, 3, 1] ∧ LexLE [2, 1, 3, 1] [1, 3, 1, 2])) h)
                    · intro q
                      exact Fin.elim0 q
          · exact by
              constructor
              · exact by
                  intro _
                  exact k16t8_cover1057
              · intro q
                exact Fin.elim0 q
    · exact by
        constructor
        · exact by
            intro _
            exact k16t8_cover1058
        · intro q
          fin_cases q
          · exact by
              constructor
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [1] [2, 2, 1] ∧ LexLE [2, 2, 1] [1, 2, 2])) h)
              · intro q
                fin_cases q
                · exact by
                    constructor
                    · exact by
                        intro h
                        exact False.elim ((by decide : ¬ (LexLE [1] [2, 2, 1, 1] ∧ LexLE [2, 2, 1, 1] [1, 1, 2, 2])) h)
                    · intro q
                      fin_cases q
                      · exact by
                          intro h
                          exact False.elim ((by decide : ¬ (LexLE [1] [2, 2, 1, 1, 1] ∧ LexLE [2, 2, 1, 1, 1] [1, 1, 1, 2, 2])) h)
                · exact by
                    constructor
                    · exact by
                        intro h
                        exact False.elim ((by decide : ¬ (LexLE [1] [2, 2, 1, 2] ∧ LexLE [2, 2, 1, 2] [2, 1, 2, 2])) h)
                    · intro q
                      exact Fin.elim0 q
          · exact by
              constructor
              · exact by
                  intro _
                  exact k16t8_cover1060
              · intro q
                fin_cases q
                · exact by
                    constructor
                    · exact by
                        intro h
                        exact False.elim ((by decide : ¬ (LexLE [1] [2, 2, 2, 1] ∧ LexLE [2, 2, 2, 1] [1, 2, 2, 2])) h)
                    · intro q
                      exact Fin.elim0 q
          · exact by
              constructor
              · exact by
                  intro _
                  exact k16t8_cover1061
              · intro q
                exact Fin.elim0 q
    · exact by
        constructor
        · exact by
            intro _
            exact k16t8_cover1062
        · intro q
          fin_cases q
          · exact by
              constructor
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [1] [2, 3, 1] ∧ LexLE [2, 3, 1] [1, 3, 2])) h)
              · intro q
                fin_cases q
                · exact by
                    constructor
                    · exact by
                        intro h
                        exact False.elim ((by decide : ¬ (LexLE [1] [2, 3, 1, 1] ∧ LexLE [2, 3, 1, 1] [1, 1, 3, 2])) h)
                    · intro q
                      exact Fin.elim0 q
          · exact by
              constructor
              · exact by
                  intro _
                  exact k16t8_cover1063
              · intro q
                exact Fin.elim0 q
    · exact by
        constructor
        · exact by
            intro _
            exact k16t8_cover1064
        · intro q
          fin_cases q
          · exact by
              constructor
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [1] [2, 4, 1] ∧ LexLE [2, 4, 1] [1, 4, 2])) h)
              · intro q
                exact Fin.elim0 q
    · exact by
        constructor
        · exact by
            intro _
            exact k16t8_cover1065
        · intro q
          exact Fin.elim0 q

private theorem k16t8_cover1067 : ∀ P ∈ pathPatterns 2 1 [3], HasCheckedCertificate 16 8 ([[1], [3], [3]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [3] [] ∧ LexLE [] [])) h)
      · intro q
        fin_cases q
        · exact by
            intro h
            exact False.elim ((by decide : ¬ (LexLE [3] [1] ∧ LexLE [1] [1])) h)

private theorem k16t8_cover1068 : ∀ P ∈ pathPatterns 2 0 [4], HasCheckedCertificate 16 8 ([[1], [3], [4]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [4] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k16t8_cover1066 : ∀ P ∈ pathPatterns 4 4 [3], HasCheckedCertificate 16 8 ([[1], [3]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [3] [] ∧ LexLE [] [])) h)
      · intro q
        fin_cases q
        · exact by
            constructor
            · exact by
                intro h
                exact False.elim ((by decide : ¬ (LexLE [3] [1] ∧ LexLE [1] [1])) h)
            · intro q
              fin_cases q
              · exact by
                  constructor
                  · exact by
                      intro h
                      exact False.elim ((by decide : ¬ (LexLE [3] [1, 1] ∧ LexLE [1, 1] [1, 1])) h)
                  · intro q
                    fin_cases q
                    · exact by
                        intro h
                        exact False.elim ((by decide : ¬ (LexLE [3] [1, 1, 1] ∧ LexLE [1, 1, 1] [1, 1, 1])) h)
                    · exact by
                        intro h
                        exact False.elim ((by decide : ¬ (LexLE [3] [1, 1, 2] ∧ LexLE [1, 1, 2] [2, 1, 1])) h)
              · exact by
                  constructor
                  · exact by
                      intro h
                      exact False.elim ((by decide : ¬ (LexLE [3] [1, 2] ∧ LexLE [1, 2] [2, 1])) h)
                  · intro q
                    fin_cases q
                    · exact by
                        intro h
                        exact False.elim ((by decide : ¬ (LexLE [3] [1, 2, 1] ∧ LexLE [1, 2, 1] [1, 2, 1])) h)
              · exact by
                  constructor
                  · exact by
                      intro h
                      exact False.elim ((by decide : ¬ (LexLE [3] [1, 3] ∧ LexLE [1, 3] [3, 1])) h)
                  · intro q
                    exact Fin.elim0 q
        · exact by
            constructor
            · exact by
                intro h
                exact False.elim ((by decide : ¬ (LexLE [3] [2] ∧ LexLE [2] [2])) h)
            · intro q
              fin_cases q
              · exact by
                  constructor
                  · exact by
                      intro h
                      exact False.elim ((by decide : ¬ (LexLE [3] [2, 1] ∧ LexLE [2, 1] [1, 2])) h)
                  · intro q
                    fin_cases q
                    · exact by
                        intro h
                        exact False.elim ((by decide : ¬ (LexLE [3] [2, 1, 1] ∧ LexLE [2, 1, 1] [1, 1, 2])) h)
              · exact by
                  constructor
                  · exact by
                      intro h
                      exact False.elim ((by decide : ¬ (LexLE [3] [2, 2] ∧ LexLE [2, 2] [2, 2])) h)
                  · intro q
                    exact Fin.elim0 q
        · exact by
            constructor
            · exact by
                intro _
                exact k16t8_cover1067
            · intro q
              fin_cases q
              · exact by
                  constructor
                  · exact by
                      intro h
                      exact False.elim ((by decide : ¬ (LexLE [3] [3, 1] ∧ LexLE [3, 1] [1, 3])) h)
                  · intro q
                    exact Fin.elim0 q
        · exact by
            constructor
            · exact by
                intro _
                exact k16t8_cover1068
            · intro q
              exact Fin.elim0 q

private theorem k16t8_cover1069 : ∀ P ∈ pathPatterns 2 0 [3, 1, 3], HasCheckedCertificate 16 8 ([[1], [3, 1, 3]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [3, 1, 3] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k16t8_cover1070 : ∀ P ∈ pathPatterns 3 1 [3, 3], HasCheckedCertificate 16 8 ([[1], [3, 3]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [3, 3] [] ∧ LexLE [] [])) h)
      · intro q
        fin_cases q
        · exact by
            constructor
            · exact by
                intro h
                exact False.elim ((by decide : ¬ (LexLE [3, 3] [1] ∧ LexLE [1] [1])) h)
            · intro q
              exact Fin.elim0 q

private theorem k16t8_cover1071 : ∀ P ∈ pathPatterns 3 0 [3, 4], HasCheckedCertificate 16 8 ([[1], [3, 4]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [3, 4] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k16t8_cover1072 : ∀ P ∈ pathPatterns 4 3 [4], HasCheckedCertificate 16 8 ([[1], [4]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [4] [] ∧ LexLE [] [])) h)
      · intro q
        fin_cases q
        · exact by
            constructor
            · exact by
                intro h
                exact False.elim ((by decide : ¬ (LexLE [4] [1] ∧ LexLE [1] [1])) h)
            · intro q
              fin_cases q
              · exact by
                  constructor
                  · exact by
                      intro h
                      exact False.elim ((by decide : ¬ (LexLE [4] [1, 1] ∧ LexLE [1, 1] [1, 1])) h)
                  · intro q
                    fin_cases q
                    · exact by
                        intro h
                        exact False.elim ((by decide : ¬ (LexLE [4] [1, 1, 1] ∧ LexLE [1, 1, 1] [1, 1, 1])) h)
              · exact by
                  constructor
                  · exact by
                      intro h
                      exact False.elim ((by decide : ¬ (LexLE [4] [1, 2] ∧ LexLE [1, 2] [2, 1])) h)
                  · intro q
                    exact Fin.elim0 q
        · exact by
            constructor
            · exact by
                intro h
                exact False.elim ((by decide : ¬ (LexLE [4] [2] ∧ LexLE [2] [2])) h)
            · intro q
              fin_cases q
              · exact by
                  constructor
                  · exact by
                      intro h
                      exact False.elim ((by decide : ¬ (LexLE [4] [2, 1] ∧ LexLE [2, 1] [1, 2])) h)
                  · intro q
                    exact Fin.elim0 q
        · exact by
            constructor
            · exact by
                intro h
                exact False.elim ((by decide : ¬ (LexLE [4] [3] ∧ LexLE [3] [3])) h)
            · intro q
              exact Fin.elim0 q

private theorem k16t8_cover1073 : ∀ P ∈ pathPatterns 4 2 [5], HasCheckedCertificate 16 8 ([[1], [5]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [5] [] ∧ LexLE [] [])) h)
      · intro q
        fin_cases q
        · exact by
            constructor
            · exact by
                intro h
                exact False.elim ((by decide : ¬ (LexLE [5] [1] ∧ LexLE [1] [1])) h)
            · intro q
              fin_cases q
              · exact by
                  constructor
                  · exact by
                      intro h
                      exact False.elim ((by decide : ¬ (LexLE [5] [1, 1] ∧ LexLE [1, 1] [1, 1])) h)
                  · intro q
                    exact Fin.elim0 q
        · exact by
            constructor
            · exact by
                intro h
                exact False.elim ((by decide : ¬ (LexLE [5] [2] ∧ LexLE [2] [2])) h)
            · intro q
              exact Fin.elim0 q

private theorem k16t8_cover1074 : ∀ P ∈ pathPatterns 4 1 [6], HasCheckedCertificate 16 8 ([[1], [6]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [6] [] ∧ LexLE [] [])) h)
      · intro q
        fin_cases q
        · exact by
            constructor
            · exact by
                intro h
                exact False.elim ((by decide : ¬ (LexLE [6] [1] ∧ LexLE [1] [1])) h)
            · intro q
              exact Fin.elim0 q

private theorem k16t8_cover1075 : ∀ P ∈ pathPatterns 4 0 [7], HasCheckedCertificate 16 8 ([[1], [7]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [7] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k16t8_seq919 : amountSequenceForall 5 7 (fun tail =>
    (LexLE [1] ([] ++ tail) ∧ LexLE ([] ++ tail) ([] ++ tail).reverse) →
    ∀ P ∈ pathPatterns (5 - ([] ++ tail).length) (7 - ([] ++ tail).sum) ([] ++ tail),
      HasCheckedCertificate 16 8 ([[1]] ++ (([] ++ tail) :: P))) :=
by
  constructor
  · exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [1] [] ∧ LexLE [] [])) h)
  · intro q
    fin_cases q
    · exact k16t8_seq920

    · exact k16t8_seq1039

    · exact by
        constructor
        · exact by
            intro _
            exact k16t8_cover1066
        · intro q
          fin_cases q
          · exact by
              constructor
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [1] [3, 1] ∧ LexLE [3, 1] [1, 3])) h)
              · intro q
                fin_cases q
                · exact by
                    constructor
                    · exact by
                        intro h
                        exact False.elim ((by decide : ¬ (LexLE [1] [3, 1, 1] ∧ LexLE [3, 1, 1] [1, 1, 3])) h)
                    · intro q
                      fin_cases q
                      · exact by
                          constructor
                          · exact by
                              intro h
                              exact False.elim ((by decide : ¬ (LexLE [1] [3, 1, 1, 1] ∧ LexLE [3, 1, 1, 1] [1, 1, 1, 3])) h)
                          · intro q
                            fin_cases q
                            · exact by
                                intro h
                                exact False.elim ((by decide : ¬ (LexLE [1] [3, 1, 1, 1, 1] ∧ LexLE [3, 1, 1, 1, 1] [1, 1, 1, 1, 3])) h)
                      · exact by
                          constructor
                          · exact by
                              intro h
                              exact False.elim ((by decide : ¬ (LexLE [1] [3, 1, 1, 2] ∧ LexLE [3, 1, 1, 2] [2, 1, 1, 3])) h)
                          · intro q
                            exact Fin.elim0 q
                · exact by
                    constructor
                    · exact by
                        intro h
                        exact False.elim ((by decide : ¬ (LexLE [1] [3, 1, 2] ∧ LexLE [3, 1, 2] [2, 1, 3])) h)
                    · intro q
                      fin_cases q
                      · exact by
                          constructor
                          · exact by
                              intro h
                              exact False.elim ((by decide : ¬ (LexLE [1] [3, 1, 2, 1] ∧ LexLE [3, 1, 2, 1] [1, 2, 1, 3])) h)
                          · intro q
                            exact Fin.elim0 q
                · exact by
                    constructor
                    · exact by
                        intro _
                        exact k16t8_cover1069
                    · intro q
                      exact Fin.elim0 q
          · exact by
              constructor
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [1] [3, 2] ∧ LexLE [3, 2] [2, 3])) h)
              · intro q
                fin_cases q
                · exact by
                    constructor
                    · exact by
                        intro h
                        exact False.elim ((by decide : ¬ (LexLE [1] [3, 2, 1] ∧ LexLE [3, 2, 1] [1, 2, 3])) h)
                    · intro q
                      fin_cases q
                      · exact by
                          constructor
                          · exact by
                              intro h
                              exact False.elim ((by decide : ¬ (LexLE [1] [3, 2, 1, 1] ∧ LexLE [3, 2, 1, 1] [1, 1, 2, 3])) h)
                          · intro q
                            exact Fin.elim0 q
                · exact by
                    constructor
                    · exact by
                        intro h
                        exact False.elim ((by decide : ¬ (LexLE [1] [3, 2, 2] ∧ LexLE [3, 2, 2] [2, 2, 3])) h)
                    · intro q
                      exact Fin.elim0 q
          · exact by
              constructor
              · exact by
                  intro _
                  exact k16t8_cover1070
              · intro q
                fin_cases q
                · exact by
                    constructor
                    · exact by
                        intro h
                        exact False.elim ((by decide : ¬ (LexLE [1] [3, 3, 1] ∧ LexLE [3, 3, 1] [1, 3, 3])) h)
                    · intro q
                      exact Fin.elim0 q
          · exact by
              constructor
              · exact by
                  intro _
                  exact k16t8_cover1071
              · intro q
                exact Fin.elim0 q
    · exact by
        constructor
        · exact by
            intro _
            exact k16t8_cover1072
        · intro q
          fin_cases q
          · exact by
              constructor
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [1] [4, 1] ∧ LexLE [4, 1] [1, 4])) h)
              · intro q
                fin_cases q
                · exact by
                    constructor
                    · exact by
                        intro h
                        exact False.elim ((by decide : ¬ (LexLE [1] [4, 1, 1] ∧ LexLE [4, 1, 1] [1, 1, 4])) h)
                    · intro q
                      fin_cases q
                      · exact by
                          constructor
                          · exact by
                              intro h
                              exact False.elim ((by decide : ¬ (LexLE [1] [4, 1, 1, 1] ∧ LexLE [4, 1, 1, 1] [1, 1, 1, 4])) h)
                          · intro q
                            exact Fin.elim0 q
                · exact by
                    constructor
                    · exact by
                        intro h
                        exact False.elim ((by decide : ¬ (LexLE [1] [4, 1, 2] ∧ LexLE [4, 1, 2] [2, 1, 4])) h)
                    · intro q
                      exact Fin.elim0 q
          · exact by
              constructor
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [1] [4, 2] ∧ LexLE [4, 2] [2, 4])) h)
              · intro q
                fin_cases q
                · exact by
                    constructor
                    · exact by
                        intro h
                        exact False.elim ((by decide : ¬ (LexLE [1] [4, 2, 1] ∧ LexLE [4, 2, 1] [1, 2, 4])) h)
                    · intro q
                      exact Fin.elim0 q
          · exact by
              constructor
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [1] [4, 3] ∧ LexLE [4, 3] [3, 4])) h)
              · intro q
                exact Fin.elim0 q
    · exact by
        constructor
        · exact by
            intro _
            exact k16t8_cover1073
        · intro q
          fin_cases q
          · exact by
              constructor
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [1] [5, 1] ∧ LexLE [5, 1] [1, 5])) h)
              · intro q
                fin_cases q
                · exact by
                    constructor
                    · exact by
                        intro h
                        exact False.elim ((by decide : ¬ (LexLE [1] [5, 1, 1] ∧ LexLE [5, 1, 1] [1, 1, 5])) h)
                    · intro q
                      exact Fin.elim0 q
          · exact by
              constructor
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [1] [5, 2] ∧ LexLE [5, 2] [2, 5])) h)
              · intro q
                exact Fin.elim0 q
    · exact by
        constructor
        · exact by
            intro _
            exact k16t8_cover1074
        · intro q
          fin_cases q
          · exact by
              constructor
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [1] [6, 1] ∧ LexLE [6, 1] [1, 6])) h)
              · intro q
                exact Fin.elim0 q
    · exact by
        constructor
        · exact by
            intro _
            exact k16t8_cover1075
        · intro q
          exact Fin.elim0 q

private theorem k16t8_cover918 : ∀ P ∈ pathPatterns 6 7 [1], HasCheckedCertificate 16 8 ([[1]] ++ P) := by
  apply pathPatterns_forall_step
  exact k16t8_seq919


private theorem k16t8_cover1081 : ∀ P ∈ pathPatterns 0 2 [2], HasCheckedCertificate 16 8 ([[1, 1], [1, 1], [2]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k16t8p421, Certificates.k16t8p421_check⟩

private theorem k16t8_cover1082 : ∀ P ∈ pathPatterns 0 1 [3], HasCheckedCertificate 16 8 ([[1, 1], [1, 1], [3]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k16t8p422, Certificates.k16t8p422_check⟩

private theorem k16t8_cover1083 : ∀ P ∈ pathPatterns 0 0 [4], HasCheckedCertificate 16 8 ([[1, 1], [1, 1], [4]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k16t8p423, Certificates.k16t8p423_check⟩

private theorem k16t8_cover1080 : ∀ P ∈ pathPatterns 2 4 [1, 1], HasCheckedCertificate 16 8 ([[1, 1], [1, 1]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [1, 1] [] ∧ LexLE [] [])) h)
      · intro q
        fin_cases q
        · exact by
            intro h
            exact False.elim ((by decide : ¬ (LexLE [1, 1] [1] ∧ LexLE [1] [1])) h)
        · exact by
            intro _
            exact k16t8_cover1081
        · exact by
            intro _
            exact k16t8_cover1082
        · exact by
            intro _
            exact k16t8_cover1083

private theorem k16t8_cover1084 : ∀ P ∈ pathPatterns 1 3 [1, 1, 1], HasCheckedCertificate 16 8 ([[1, 1], [1, 1, 1]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [1, 1, 1] [] ∧ LexLE [] [])) h)

private theorem k16t8_cover1085 : ∀ P ∈ pathPatterns 0 2 [1, 1, 1, 1], HasCheckedCertificate 16 8 ([[1, 1], [1, 1, 1, 1]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k16t8p424, Certificates.k16t8p424_check⟩

private theorem k16t8_cover1086 : ∀ P ∈ pathPatterns 0 1 [1, 1, 1, 2], HasCheckedCertificate 16 8 ([[1, 1], [1, 1, 1, 2]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k16t8p425, Certificates.k16t8p425_check⟩

private theorem k16t8_cover1087 : ∀ P ∈ pathPatterns 0 0 [1, 1, 1, 3], HasCheckedCertificate 16 8 ([[1, 1], [1, 1, 1, 3]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k16t8p426, Certificates.k16t8p426_check⟩

private theorem k16t8_cover1088 : ∀ P ∈ pathPatterns 1 2 [1, 1, 2], HasCheckedCertificate 16 8 ([[1, 1], [1, 1, 2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [1, 1, 2] [] ∧ LexLE [] [])) h)

private theorem k16t8_cover1089 : ∀ P ∈ pathPatterns 0 1 [1, 1, 2, 1], HasCheckedCertificate 16 8 ([[1, 1], [1, 1, 2, 1]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k16t8p427, Certificates.k16t8p427_check⟩

private theorem k16t8_cover1090 : ∀ P ∈ pathPatterns 0 0 [1, 1, 2, 2], HasCheckedCertificate 16 8 ([[1, 1], [1, 1, 2, 2]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k16t8p428, Certificates.k16t8p428_check⟩

private theorem k16t8_cover1091 : ∀ P ∈ pathPatterns 1 1 [1, 1, 3], HasCheckedCertificate 16 8 ([[1, 1], [1, 1, 3]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [1, 1, 3] [] ∧ LexLE [] [])) h)

private theorem k16t8_cover1092 : ∀ P ∈ pathPatterns 0 0 [1, 1, 3, 1], HasCheckedCertificate 16 8 ([[1, 1], [1, 1, 3, 1]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k16t8p429, Certificates.k16t8p429_check⟩

private theorem k16t8_cover1093 : ∀ P ∈ pathPatterns 1 0 [1, 1, 4], HasCheckedCertificate 16 8 ([[1, 1], [1, 1, 4]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [1, 1, 4] [] ∧ LexLE [] [])) h)

private theorem k16t8_cover1095 : ∀ P ∈ pathPatterns 0 1 [2], HasCheckedCertificate 16 8 ([[1, 1], [1, 2], [2]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k16t8p430, Certificates.k16t8p430_check⟩

private theorem k16t8_cover1096 : ∀ P ∈ pathPatterns 0 0 [3], HasCheckedCertificate 16 8 ([[1, 1], [1, 2], [3]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k16t8p431, Certificates.k16t8p431_check⟩

private theorem k16t8_cover1094 : ∀ P ∈ pathPatterns 2 3 [1, 2], HasCheckedCertificate 16 8 ([[1, 1], [1, 2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [1, 2] [] ∧ LexLE [] [])) h)
      · intro q
        fin_cases q
        · exact by
            intro h
            exact False.elim ((by decide : ¬ (LexLE [1, 2] [1] ∧ LexLE [1] [1])) h)
        · exact by
            intro _
            exact k16t8_cover1095
        · exact by
            intro _
            exact k16t8_cover1096

private theorem k16t8_cover1097 : ∀ P ∈ pathPatterns 1 2 [1, 2, 1], HasCheckedCertificate 16 8 ([[1, 1], [1, 2, 1]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [1, 2, 1] [] ∧ LexLE [] [])) h)

private theorem k16t8_cover1098 : ∀ P ∈ pathPatterns 0 0 [1, 2, 1, 2], HasCheckedCertificate 16 8 ([[1, 1], [1, 2, 1, 2]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k16t8p432, Certificates.k16t8p432_check⟩

private theorem k16t8_cover1099 : ∀ P ∈ pathPatterns 1 1 [1, 2, 2], HasCheckedCertificate 16 8 ([[1, 1], [1, 2, 2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [1, 2, 2] [] ∧ LexLE [] [])) h)

private theorem k16t8_cover1100 : ∀ P ∈ pathPatterns 0 0 [1, 2, 2, 1], HasCheckedCertificate 16 8 ([[1, 1], [1, 2, 2, 1]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k16t8p433, Certificates.k16t8p433_check⟩

private theorem k16t8_cover1101 : ∀ P ∈ pathPatterns 1 0 [1, 2, 3], HasCheckedCertificate 16 8 ([[1, 1], [1, 2, 3]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [1, 2, 3] [] ∧ LexLE [] [])) h)

private theorem k16t8_cover1103 : ∀ P ∈ pathPatterns 0 0 [2], HasCheckedCertificate 16 8 ([[1, 1], [1, 3], [2]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k16t8p434, Certificates.k16t8p434_check⟩

private theorem k16t8_cover1102 : ∀ P ∈ pathPatterns 2 2 [1, 3], HasCheckedCertificate 16 8 ([[1, 1], [1, 3]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [1, 3] [] ∧ LexLE [] [])) h)
      · intro q
        fin_cases q
        · exact by
            intro h
            exact False.elim ((by decide : ¬ (LexLE [1, 3] [1] ∧ LexLE [1] [1])) h)
        · exact by
            intro _
            exact k16t8_cover1103

private theorem k16t8_cover1104 : ∀ P ∈ pathPatterns 1 1 [1, 3, 1], HasCheckedCertificate 16 8 ([[1, 1], [1, 3, 1]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [1, 3, 1] [] ∧ LexLE [] [])) h)

private theorem k16t8_cover1105 : ∀ P ∈ pathPatterns 1 0 [1, 3, 2], HasCheckedCertificate 16 8 ([[1, 1], [1, 3, 2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [1, 3, 2] [] ∧ LexLE [] [])) h)

private theorem k16t8_cover1106 : ∀ P ∈ pathPatterns 2 1 [1, 4], HasCheckedCertificate 16 8 ([[1, 1], [1, 4]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [1, 4] [] ∧ LexLE [] [])) h)
      · intro q
        fin_cases q
        · exact by
            intro h
            exact False.elim ((by decide : ¬ (LexLE [1, 4] [1] ∧ LexLE [1] [1])) h)

private theorem k16t8_cover1107 : ∀ P ∈ pathPatterns 1 0 [1, 4, 1], HasCheckedCertificate 16 8 ([[1, 1], [1, 4, 1]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [1, 4, 1] [] ∧ LexLE [] [])) h)

private theorem k16t8_cover1108 : ∀ P ∈ pathPatterns 2 0 [1, 5], HasCheckedCertificate 16 8 ([[1, 1], [1, 5]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [1, 5] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k16t8_seq1079 : amountSequenceForall 3 5 (fun tail =>
    (LexLE [1, 1] ([1] ++ tail) ∧ LexLE ([1] ++ tail) ([1] ++ tail).reverse) →
    ∀ P ∈ pathPatterns (4 - ([1] ++ tail).length) (6 - ([1] ++ tail).sum) ([1] ++ tail),
      HasCheckedCertificate 16 8 ([[1, 1]] ++ (([1] ++ tail) :: P))) :=
by
  constructor
  · exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [1, 1] [1] ∧ LexLE [1] [1])) h)
  · intro q
    fin_cases q
    · exact by
        constructor
        · exact by
            intro _
            exact k16t8_cover1080
        · intro q
          fin_cases q
          · exact by
              constructor
              · exact by
                  intro _
                  exact k16t8_cover1084
              · intro q
                fin_cases q
                · exact by
                    intro _
                    exact k16t8_cover1085
                · exact by
                    intro _
                    exact k16t8_cover1086
                · exact by
                    intro _
                    exact k16t8_cover1087
          · exact by
              constructor
              · exact by
                  intro _
                  exact k16t8_cover1088
              · intro q
                fin_cases q
                · exact by
                    intro _
                    exact k16t8_cover1089
                · exact by
                    intro _
                    exact k16t8_cover1090
          · exact by
              constructor
              · exact by
                  intro _
                  exact k16t8_cover1091
              · intro q
                fin_cases q
                · exact by
                    intro _
                    exact k16t8_cover1092
          · exact by
              constructor
              · exact by
                  intro _
                  exact k16t8_cover1093
              · intro q
                exact Fin.elim0 q
    · exact by
        constructor
        · exact by
            intro _
            exact k16t8_cover1094
        · intro q
          fin_cases q
          · exact by
              constructor
              · exact by
                  intro _
                  exact k16t8_cover1097
              · intro q
                fin_cases q
                · exact by
                    intro h
                    exact False.elim ((by decide : ¬ (LexLE [1, 1] [1, 2, 1, 1] ∧ LexLE [1, 2, 1, 1] [1, 1, 2, 1])) h)
                · exact by
                    intro _
                    exact k16t8_cover1098
          · exact by
              constructor
              · exact by
                  intro _
                  exact k16t8_cover1099
              · intro q
                fin_cases q
                · exact by
                    intro _
                    exact k16t8_cover1100
          · exact by
              constructor
              · exact by
                  intro _
                  exact k16t8_cover1101
              · intro q
                exact Fin.elim0 q
    · exact by
        constructor
        · exact by
            intro _
            exact k16t8_cover1102
        · intro q
          fin_cases q
          · exact by
              constructor
              · exact by
                  intro _
                  exact k16t8_cover1104
              · intro q
                fin_cases q
                · exact by
                    intro h
                    exact False.elim ((by decide : ¬ (LexLE [1, 1] [1, 3, 1, 1] ∧ LexLE [1, 3, 1, 1] [1, 1, 3, 1])) h)
          · exact by
              constructor
              · exact by
                  intro _
                  exact k16t8_cover1105
              · intro q
                exact Fin.elim0 q
    · exact by
        constructor
        · exact by
            intro _
            exact k16t8_cover1106
        · intro q
          fin_cases q
          · exact by
              constructor
              · exact by
                  intro _
                  exact k16t8_cover1107
              · intro q
                exact Fin.elim0 q
    · exact by
        constructor
        · exact by
            intro _
            exact k16t8_cover1108
        · intro q
          exact Fin.elim0 q

private theorem k16t8_cover1110 : ∀ P ∈ pathPatterns 1 2 [2], HasCheckedCertificate 16 8 ([[1, 1], [2], [2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [2] [] ∧ LexLE [] [])) h)

private theorem k16t8_cover1111 : ∀ P ∈ pathPatterns 0 0 [2, 2], HasCheckedCertificate 16 8 ([[1, 1], [2], [2, 2]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k16t8p435, Certificates.k16t8p435_check⟩

private theorem k16t8_cover1112 : ∀ P ∈ pathPatterns 1 1 [3], HasCheckedCertificate 16 8 ([[1, 1], [2], [3]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [3] [] ∧ LexLE [] [])) h)

private theorem k16t8_cover1113 : ∀ P ∈ pathPatterns 1 0 [4], HasCheckedCertificate 16 8 ([[1, 1], [2], [4]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [4] [] ∧ LexLE [] [])) h)

private theorem k16t8_cover1109 : ∀ P ∈ pathPatterns 3 4 [2], HasCheckedCertificate 16 8 ([[1, 1], [2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [2] [] ∧ LexLE [] [])) h)
      · intro q
        fin_cases q
        · exact by
            constructor
            · exact by
                intro h
                exact False.elim ((by decide : ¬ (LexLE [2] [1] ∧ LexLE [1] [1])) h)
            · intro q
              fin_cases q
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [2] [1, 1] ∧ LexLE [1, 1] [1, 1])) h)
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [2] [1, 2] ∧ LexLE [1, 2] [2, 1])) h)
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [2] [1, 3] ∧ LexLE [1, 3] [3, 1])) h)
        · exact by
            constructor
            · exact by
                intro _
                exact k16t8_cover1110
            · intro q
              fin_cases q
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [2] [2, 1] ∧ LexLE [2, 1] [1, 2])) h)
              · exact by
                  intro _
                  exact k16t8_cover1111
        · exact by
            constructor
            · exact by
                intro _
                exact k16t8_cover1112
            · intro q
              fin_cases q
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [2] [3, 1] ∧ LexLE [3, 1] [1, 3])) h)
        · exact by
            constructor
            · exact by
                intro _
                exact k16t8_cover1113
            · intro q
              exact Fin.elim0 q

private theorem k16t8_cover1114 : ∀ P ∈ pathPatterns 0 0 [2, 1, 1, 2], HasCheckedCertificate 16 8 ([[1, 1], [2, 1, 1, 2]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k16t8p436, Certificates.k16t8p436_check⟩

private theorem k16t8_cover1115 : ∀ P ∈ pathPatterns 1 1 [2, 1, 2], HasCheckedCertificate 16 8 ([[1, 1], [2, 1, 2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [2, 1, 2] [] ∧ LexLE [] [])) h)

private theorem k16t8_cover1116 : ∀ P ∈ pathPatterns 1 0 [2, 1, 3], HasCheckedCertificate 16 8 ([[1, 1], [2, 1, 3]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [2, 1, 3] [] ∧ LexLE [] [])) h)

private theorem k16t8_cover1117 : ∀ P ∈ pathPatterns 2 2 [2, 2], HasCheckedCertificate 16 8 ([[1, 1], [2, 2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [2, 2] [] ∧ LexLE [] [])) h)
      · intro q
        fin_cases q
        · exact by
            intro h
            exact False.elim ((by decide : ¬ (LexLE [2, 2] [1] ∧ LexLE [1] [1])) h)
        · exact by
            intro h
            exact False.elim ((by decide : ¬ (LexLE [2, 2] [2] ∧ LexLE [2] [2])) h)

private theorem k16t8_cover1118 : ∀ P ∈ pathPatterns 1 0 [2, 2, 2], HasCheckedCertificate 16 8 ([[1, 1], [2, 2, 2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [2, 2, 2] [] ∧ LexLE [] [])) h)

private theorem k16t8_cover1119 : ∀ P ∈ pathPatterns 2 1 [2, 3], HasCheckedCertificate 16 8 ([[1, 1], [2, 3]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [2, 3] [] ∧ LexLE [] [])) h)
      · intro q
        fin_cases q
        · exact by
            intro h
            exact False.elim ((by decide : ¬ (LexLE [2, 3] [1] ∧ LexLE [1] [1])) h)

private theorem k16t8_cover1120 : ∀ P ∈ pathPatterns 2 0 [2, 4], HasCheckedCertificate 16 8 ([[1, 1], [2, 4]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [2, 4] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k16t8_cover1122 : ∀ P ∈ pathPatterns 1 0 [3], HasCheckedCertificate 16 8 ([[1, 1], [3], [3]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [3] [] ∧ LexLE [] [])) h)

private theorem k16t8_cover1121 : ∀ P ∈ pathPatterns 3 3 [3], HasCheckedCertificate 16 8 ([[1, 1], [3]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [3] [] ∧ LexLE [] [])) h)
      · intro q
        fin_cases q
        · exact by
            constructor
            · exact by
                intro h
                exact False.elim ((by decide : ¬ (LexLE [3] [1] ∧ LexLE [1] [1])) h)
            · intro q
              fin_cases q
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [3] [1, 1] ∧ LexLE [1, 1] [1, 1])) h)
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [3] [1, 2] ∧ LexLE [1, 2] [2, 1])) h)
        · exact by
            constructor
            · exact by
                intro h
                exact False.elim ((by decide : ¬ (LexLE [3] [2] ∧ LexLE [2] [2])) h)
            · intro q
              fin_cases q
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [3] [2, 1] ∧ LexLE [2, 1] [1, 2])) h)
        · exact by
            constructor
            · exact by
                intro _
                exact k16t8_cover1122
            · intro q
              exact Fin.elim0 q

private theorem k16t8_cover1123 : ∀ P ∈ pathPatterns 2 0 [3, 3], HasCheckedCertificate 16 8 ([[1, 1], [3, 3]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [3, 3] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k16t8_cover1124 : ∀ P ∈ pathPatterns 3 2 [4], HasCheckedCertificate 16 8 ([[1, 1], [4]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [4] [] ∧ LexLE [] [])) h)
      · intro q
        fin_cases q
        · exact by
            constructor
            · exact by
                intro h
                exact False.elim ((by decide : ¬ (LexLE [4] [1] ∧ LexLE [1] [1])) h)
            · intro q
              fin_cases q
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [4] [1, 1] ∧ LexLE [1, 1] [1, 1])) h)
        · exact by
            constructor
            · exact by
                intro h
                exact False.elim ((by decide : ¬ (LexLE [4] [2] ∧ LexLE [2] [2])) h)
            · intro q
              exact Fin.elim0 q

private theorem k16t8_cover1125 : ∀ P ∈ pathPatterns 3 1 [5], HasCheckedCertificate 16 8 ([[1, 1], [5]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [5] [] ∧ LexLE [] [])) h)
      · intro q
        fin_cases q
        · exact by
            constructor
            · exact by
                intro h
                exact False.elim ((by decide : ¬ (LexLE [5] [1] ∧ LexLE [1] [1])) h)
            · intro q
              exact Fin.elim0 q

private theorem k16t8_cover1126 : ∀ P ∈ pathPatterns 3 0 [6], HasCheckedCertificate 16 8 ([[1, 1], [6]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [6] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k16t8_seq1078 : amountSequenceForall 4 6 (fun tail =>
    (LexLE [1, 1] ([] ++ tail) ∧ LexLE ([] ++ tail) ([] ++ tail).reverse) →
    ∀ P ∈ pathPatterns (4 - ([] ++ tail).length) (6 - ([] ++ tail).sum) ([] ++ tail),
      HasCheckedCertificate 16 8 ([[1, 1]] ++ (([] ++ tail) :: P))) :=
by
  constructor
  · exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [1, 1] [] ∧ LexLE [] [])) h)
  · intro q
    fin_cases q
    · exact k16t8_seq1079

    · exact by
        constructor
        · exact by
            intro _
            exact k16t8_cover1109
        · intro q
          fin_cases q
          · exact by
              constructor
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [1, 1] [2, 1] ∧ LexLE [2, 1] [1, 2])) h)
              · intro q
                fin_cases q
                · exact by
                    constructor
                    · exact by
                        intro h
                        exact False.elim ((by decide : ¬ (LexLE [1, 1] [2, 1, 1] ∧ LexLE [2, 1, 1] [1, 1, 2])) h)
                    · intro q
                      fin_cases q
                      · exact by
                          intro h
                          exact False.elim ((by decide : ¬ (LexLE [1, 1] [2, 1, 1, 1] ∧ LexLE [2, 1, 1, 1] [1, 1, 1, 2])) h)
                      · exact by
                          intro _
                          exact k16t8_cover1114
                · exact by
                    constructor
                    · exact by
                        intro _
                        exact k16t8_cover1115
                    · intro q
                      fin_cases q
                      · exact by
                          intro h
                          exact False.elim ((by decide : ¬ (LexLE [1, 1] [2, 1, 2, 1] ∧ LexLE [2, 1, 2, 1] [1, 2, 1, 2])) h)
                · exact by
                    constructor
                    · exact by
                        intro _
                        exact k16t8_cover1116
                    · intro q
                      exact Fin.elim0 q
          · exact by
              constructor
              · exact by
                  intro _
                  exact k16t8_cover1117
              · intro q
                fin_cases q
                · exact by
                    constructor
                    · exact by
                        intro h
                        exact False.elim ((by decide : ¬ (LexLE [1, 1] [2, 2, 1] ∧ LexLE [2, 2, 1] [1, 2, 2])) h)
                    · intro q
                      fin_cases q
                      · exact by
                          intro h
                          exact False.elim ((by decide : ¬ (LexLE [1, 1] [2, 2, 1, 1] ∧ LexLE [2, 2, 1, 1] [1, 1, 2, 2])) h)
                · exact by
                    constructor
                    · exact by
                        intro _
                        exact k16t8_cover1118
                    · intro q
                      exact Fin.elim0 q
          · exact by
              constructor
              · exact by
                  intro _
                  exact k16t8_cover1119
              · intro q
                fin_cases q
                · exact by
                    constructor
                    · exact by
                        intro h
                        exact False.elim ((by decide : ¬ (LexLE [1, 1] [2, 3, 1] ∧ LexLE [2, 3, 1] [1, 3, 2])) h)
                    · intro q
                      exact Fin.elim0 q
          · exact by
              constructor
              · exact by
                  intro _
                  exact k16t8_cover1120
              · intro q
                exact Fin.elim0 q
    · exact by
        constructor
        · exact by
            intro _
            exact k16t8_cover1121
        · intro q
          fin_cases q
          · exact by
              constructor
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [1, 1] [3, 1] ∧ LexLE [3, 1] [1, 3])) h)
              · intro q
                fin_cases q
                · exact by
                    constructor
                    · exact by
                        intro h
                        exact False.elim ((by decide : ¬ (LexLE [1, 1] [3, 1, 1] ∧ LexLE [3, 1, 1] [1, 1, 3])) h)
                    · intro q
                      fin_cases q
                      · exact by
                          intro h
                          exact False.elim ((by decide : ¬ (LexLE [1, 1] [3, 1, 1, 1] ∧ LexLE [3, 1, 1, 1] [1, 1, 1, 3])) h)
                · exact by
                    constructor
                    · exact by
                        intro h
                        exact False.elim ((by decide : ¬ (LexLE [1, 1] [3, 1, 2] ∧ LexLE [3, 1, 2] [2, 1, 3])) h)
                    · intro q
                      exact Fin.elim0 q
          · exact by
              constructor
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [1, 1] [3, 2] ∧ LexLE [3, 2] [2, 3])) h)
              · intro q
                fin_cases q
                · exact by
                    constructor
                    · exact by
                        intro h
                        exact False.elim ((by decide : ¬ (LexLE [1, 1] [3, 2, 1] ∧ LexLE [3, 2, 1] [1, 2, 3])) h)
                    · intro q
                      exact Fin.elim0 q
          · exact by
              constructor
              · exact by
                  intro _
                  exact k16t8_cover1123
              · intro q
                exact Fin.elim0 q
    · exact by
        constructor
        · exact by
            intro _
            exact k16t8_cover1124
        · intro q
          fin_cases q
          · exact by
              constructor
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [1, 1] [4, 1] ∧ LexLE [4, 1] [1, 4])) h)
              · intro q
                fin_cases q
                · exact by
                    constructor
                    · exact by
                        intro h
                        exact False.elim ((by decide : ¬ (LexLE [1, 1] [4, 1, 1] ∧ LexLE [4, 1, 1] [1, 1, 4])) h)
                    · intro q
                      exact Fin.elim0 q
          · exact by
              constructor
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [1, 1] [4, 2] ∧ LexLE [4, 2] [2, 4])) h)
              · intro q
                exact Fin.elim0 q
    · exact by
        constructor
        · exact by
            intro _
            exact k16t8_cover1125
        · intro q
          fin_cases q
          · exact by
              constructor
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [1, 1] [5, 1] ∧ LexLE [5, 1] [1, 5])) h)
              · intro q
                exact Fin.elim0 q
    · exact by
        constructor
        · exact by
            intro _
            exact k16t8_cover1126
        · intro q
          exact Fin.elim0 q

private theorem k16t8_cover1077 : ∀ P ∈ pathPatterns 5 6 [1, 1], HasCheckedCertificate 16 8 ([[1, 1]] ++ P) := by
  apply pathPatterns_forall_step
  exact k16t8_seq1078


private theorem k16t8_cover1130 : ∀ P ∈ pathPatterns 0 2 [1, 1, 1], HasCheckedCertificate 16 8 ([[1, 1, 1], [1, 1, 1]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k16t8p437, Certificates.k16t8p437_check⟩

private theorem k16t8_cover1131 : ∀ P ∈ pathPatterns 0 1 [1, 1, 2], HasCheckedCertificate 16 8 ([[1, 1, 1], [1, 1, 2]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k16t8p438, Certificates.k16t8p438_check⟩

private theorem k16t8_cover1132 : ∀ P ∈ pathPatterns 0 0 [1, 1, 3], HasCheckedCertificate 16 8 ([[1, 1, 1], [1, 1, 3]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k16t8p439, Certificates.k16t8p439_check⟩

private theorem k16t8_cover1133 : ∀ P ∈ pathPatterns 1 2 [1, 2], HasCheckedCertificate 16 8 ([[1, 1, 1], [1, 2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [1, 2] [] ∧ LexLE [] [])) h)

private theorem k16t8_cover1134 : ∀ P ∈ pathPatterns 0 1 [1, 2, 1], HasCheckedCertificate 16 8 ([[1, 1, 1], [1, 2, 1]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k16t8p440, Certificates.k16t8p440_check⟩

private theorem k16t8_cover1135 : ∀ P ∈ pathPatterns 0 0 [1, 2, 2], HasCheckedCertificate 16 8 ([[1, 1, 1], [1, 2, 2]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k16t8p441, Certificates.k16t8p441_check⟩

private theorem k16t8_cover1136 : ∀ P ∈ pathPatterns 1 1 [1, 3], HasCheckedCertificate 16 8 ([[1, 1, 1], [1, 3]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [1, 3] [] ∧ LexLE [] [])) h)

private theorem k16t8_cover1137 : ∀ P ∈ pathPatterns 0 0 [1, 3, 1], HasCheckedCertificate 16 8 ([[1, 1, 1], [1, 3, 1]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k16t8p442, Certificates.k16t8p442_check⟩

private theorem k16t8_cover1138 : ∀ P ∈ pathPatterns 1 0 [1, 4], HasCheckedCertificate 16 8 ([[1, 1, 1], [1, 4]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [1, 4] [] ∧ LexLE [] [])) h)

private theorem k16t8_cover1140 : ∀ P ∈ pathPatterns 0 1 [2], HasCheckedCertificate 16 8 ([[1, 1, 1], [2], [2]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k16t8p443, Certificates.k16t8p443_check⟩

private theorem k16t8_cover1141 : ∀ P ∈ pathPatterns 0 0 [3], HasCheckedCertificate 16 8 ([[1, 1, 1], [2], [3]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k16t8p444, Certificates.k16t8p444_check⟩

private theorem k16t8_cover1139 : ∀ P ∈ pathPatterns 2 3 [2], HasCheckedCertificate 16 8 ([[1, 1, 1], [2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [2] [] ∧ LexLE [] [])) h)
      · intro q
        fin_cases q
        · exact by
            intro h
            exact False.elim ((by decide : ¬ (LexLE [2] [1] ∧ LexLE [1] [1])) h)
        · exact by
            intro _
            exact k16t8_cover1140
        · exact by
            intro _
            exact k16t8_cover1141

private theorem k16t8_cover1142 : ∀ P ∈ pathPatterns 0 0 [2, 1, 2], HasCheckedCertificate 16 8 ([[1, 1, 1], [2, 1, 2]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k16t8p445, Certificates.k16t8p445_check⟩

private theorem k16t8_cover1143 : ∀ P ∈ pathPatterns 1 1 [2, 2], HasCheckedCertificate 16 8 ([[1, 1, 1], [2, 2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [2, 2] [] ∧ LexLE [] [])) h)

private theorem k16t8_cover1144 : ∀ P ∈ pathPatterns 1 0 [2, 3], HasCheckedCertificate 16 8 ([[1, 1, 1], [2, 3]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [2, 3] [] ∧ LexLE [] [])) h)

private theorem k16t8_cover1145 : ∀ P ∈ pathPatterns 2 2 [3], HasCheckedCertificate 16 8 ([[1, 1, 1], [3]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [3] [] ∧ LexLE [] [])) h)
      · intro q
        fin_cases q
        · exact by
            intro h
            exact False.elim ((by decide : ¬ (LexLE [3] [1] ∧ LexLE [1] [1])) h)
        · exact by
            intro h
            exact False.elim ((by decide : ¬ (LexLE [3] [2] ∧ LexLE [2] [2])) h)

private theorem k16t8_cover1146 : ∀ P ∈ pathPatterns 2 1 [4], HasCheckedCertificate 16 8 ([[1, 1, 1], [4]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [4] [] ∧ LexLE [] [])) h)
      · intro q
        fin_cases q
        · exact by
            intro h
            exact False.elim ((by decide : ¬ (LexLE [4] [1] ∧ LexLE [1] [1])) h)

private theorem k16t8_cover1147 : ∀ P ∈ pathPatterns 2 0 [5], HasCheckedCertificate 16 8 ([[1, 1, 1], [5]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [5] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k16t8_seq1129 : amountSequenceForall 3 5 (fun tail =>
    (LexLE [1, 1, 1] ([] ++ tail) ∧ LexLE ([] ++ tail) ([] ++ tail).reverse) →
    ∀ P ∈ pathPatterns (3 - ([] ++ tail).length) (5 - ([] ++ tail).sum) ([] ++ tail),
      HasCheckedCertificate 16 8 ([[1, 1, 1]] ++ (([] ++ tail) :: P))) :=
by
  constructor
  · exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [1, 1, 1] [] ∧ LexLE [] [])) h)
  · intro q
    fin_cases q
    · exact by
        constructor
        · exact by
            intro h
            exact False.elim ((by decide : ¬ (LexLE [1, 1, 1] [1] ∧ LexLE [1] [1])) h)
        · intro q
          fin_cases q
          · exact by
              constructor
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [1, 1, 1] [1, 1] ∧ LexLE [1, 1] [1, 1])) h)
              · intro q
                fin_cases q
                · exact by
                    intro _
                    exact k16t8_cover1130
                · exact by
                    intro _
                    exact k16t8_cover1131
                · exact by
                    intro _
                    exact k16t8_cover1132
          · exact by
              constructor
              · exact by
                  intro _
                  exact k16t8_cover1133
              · intro q
                fin_cases q
                · exact by
                    intro _
                    exact k16t8_cover1134
                · exact by
                    intro _
                    exact k16t8_cover1135
          · exact by
              constructor
              · exact by
                  intro _
                  exact k16t8_cover1136
              · intro q
                fin_cases q
                · exact by
                    intro _
                    exact k16t8_cover1137
          · exact by
              constructor
              · exact by
                  intro _
                  exact k16t8_cover1138
              · intro q
                exact Fin.elim0 q
    · exact by
        constructor
        · exact by
            intro _
            exact k16t8_cover1139
        · intro q
          fin_cases q
          · exact by
              constructor
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [1, 1, 1] [2, 1] ∧ LexLE [2, 1] [1, 2])) h)
              · intro q
                fin_cases q
                · exact by
                    intro h
                    exact False.elim ((by decide : ¬ (LexLE [1, 1, 1] [2, 1, 1] ∧ LexLE [2, 1, 1] [1, 1, 2])) h)
                · exact by
                    intro _
                    exact k16t8_cover1142
          · exact by
              constructor
              · exact by
                  intro _
                  exact k16t8_cover1143
              · intro q
                fin_cases q
                · exact by
                    intro h
                    exact False.elim ((by decide : ¬ (LexLE [1, 1, 1] [2, 2, 1] ∧ LexLE [2, 2, 1] [1, 2, 2])) h)
          · exact by
              constructor
              · exact by
                  intro _
                  exact k16t8_cover1144
              · intro q
                exact Fin.elim0 q
    · exact by
        constructor
        · exact by
            intro _
            exact k16t8_cover1145
        · intro q
          fin_cases q
          · exact by
              constructor
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [1, 1, 1] [3, 1] ∧ LexLE [3, 1] [1, 3])) h)
              · intro q
                fin_cases q
                · exact by
                    intro h
                    exact False.elim ((by decide : ¬ (LexLE [1, 1, 1] [3, 1, 1] ∧ LexLE [3, 1, 1] [1, 1, 3])) h)
          · exact by
              constructor
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [1, 1, 1] [3, 2] ∧ LexLE [3, 2] [2, 3])) h)
              · intro q
                exact Fin.elim0 q
    · exact by
        constructor
        · exact by
            intro _
            exact k16t8_cover1146
        · intro q
          fin_cases q
          · exact by
              constructor
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [1, 1, 1] [4, 1] ∧ LexLE [4, 1] [1, 4])) h)
              · intro q
                exact Fin.elim0 q
    · exact by
        constructor
        · exact by
            intro _
            exact k16t8_cover1147
        · intro q
          exact Fin.elim0 q

private theorem k16t8_cover1128 : ∀ P ∈ pathPatterns 4 5 [1, 1, 1], HasCheckedCertificate 16 8 ([[1, 1, 1]] ++ P) := by
  apply pathPatterns_forall_step
  exact k16t8_seq1129


private theorem k16t8_cover1149 : ∀ P ∈ pathPatterns 0 1 [1, 2], HasCheckedCertificate 16 8 ([[1, 1, 1, 1], [1, 2]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k16t8p446, Certificates.k16t8p446_check⟩

private theorem k16t8_cover1150 : ∀ P ∈ pathPatterns 0 0 [1, 3], HasCheckedCertificate 16 8 ([[1, 1, 1, 1], [1, 3]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k16t8p447, Certificates.k16t8p447_check⟩

private theorem k16t8_cover1151 : ∀ P ∈ pathPatterns 1 2 [2], HasCheckedCertificate 16 8 ([[1, 1, 1, 1], [2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [2] [] ∧ LexLE [] [])) h)

private theorem k16t8_cover1152 : ∀ P ∈ pathPatterns 0 0 [2, 2], HasCheckedCertificate 16 8 ([[1, 1, 1, 1], [2, 2]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k16t8p448, Certificates.k16t8p448_check⟩

private theorem k16t8_cover1153 : ∀ P ∈ pathPatterns 1 1 [3], HasCheckedCertificate 16 8 ([[1, 1, 1, 1], [3]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [3] [] ∧ LexLE [] [])) h)

private theorem k16t8_cover1154 : ∀ P ∈ pathPatterns 1 0 [4], HasCheckedCertificate 16 8 ([[1, 1, 1, 1], [4]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [4] [] ∧ LexLE [] [])) h)

private theorem k16t8_cover1148 : ∀ P ∈ pathPatterns 3 4 [1, 1, 1, 1], HasCheckedCertificate 16 8 ([[1, 1, 1, 1]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [1, 1, 1, 1] [] ∧ LexLE [] [])) h)
      · intro q
        fin_cases q
        · exact by
            constructor
            · exact by
                intro h
                exact False.elim ((by decide : ¬ (LexLE [1, 1, 1, 1] [1] ∧ LexLE [1] [1])) h)
            · intro q
              fin_cases q
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [1, 1, 1, 1] [1, 1] ∧ LexLE [1, 1] [1, 1])) h)
              · exact by
                  intro _
                  exact k16t8_cover1149
              · exact by
                  intro _
                  exact k16t8_cover1150
        · exact by
            constructor
            · exact by
                intro _
                exact k16t8_cover1151
            · intro q
              fin_cases q
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [1, 1, 1, 1] [2, 1] ∧ LexLE [2, 1] [1, 2])) h)
              · exact by
                  intro _
                  exact k16t8_cover1152
        · exact by
            constructor
            · exact by
                intro _
                exact k16t8_cover1153
            · intro q
              fin_cases q
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [1, 1, 1, 1] [3, 1] ∧ LexLE [3, 1] [1, 3])) h)
        · exact by
            constructor
            · exact by
                intro _
                exact k16t8_cover1154
            · intro q
              exact Fin.elim0 q

private theorem k16t8_cover1156 : ∀ P ∈ pathPatterns 0 1 [2], HasCheckedCertificate 16 8 ([[1, 1, 1, 1, 1], [2]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k16t8p449, Certificates.k16t8p449_check⟩

private theorem k16t8_cover1157 : ∀ P ∈ pathPatterns 0 0 [3], HasCheckedCertificate 16 8 ([[1, 1, 1, 1, 1], [3]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k16t8p450, Certificates.k16t8p450_check⟩

private theorem k16t8_cover1155 : ∀ P ∈ pathPatterns 2 3 [1, 1, 1, 1, 1], HasCheckedCertificate 16 8 ([[1, 1, 1, 1, 1]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [1, 1, 1, 1, 1] [] ∧ LexLE [] [])) h)
      · intro q
        fin_cases q
        · exact by
            intro h
            exact False.elim ((by decide : ¬ (LexLE [1, 1, 1, 1, 1] [1] ∧ LexLE [1] [1])) h)
        · exact by
            intro _
            exact k16t8_cover1156
        · exact by
            intro _
            exact k16t8_cover1157

private theorem k16t8_cover1158 : ∀ P ∈ pathPatterns 1 2 [1, 1, 1, 1, 1, 1], HasCheckedCertificate 16 8 ([[1, 1, 1, 1, 1, 1]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [1, 1, 1, 1, 1, 1] [] ∧ LexLE [] [])) h)

private theorem k16t8_cover1159 : ∀ P ∈ pathPatterns 0 1 [1, 1, 1, 1, 1, 1, 1], HasCheckedCertificate 16 8 ([[1, 1, 1, 1, 1, 1, 1]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k16t8p451, Certificates.k16t8p451_check⟩

private theorem k16t8_cover1160 : ∀ P ∈ pathPatterns 0 0 [1, 1, 1, 1, 1, 1, 2], HasCheckedCertificate 16 8 ([[1, 1, 1, 1, 1, 1, 2]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k16t8p452, Certificates.k16t8p452_check⟩

private theorem k16t8_cover1161 : ∀ P ∈ pathPatterns 1 1 [1, 1, 1, 1, 1, 2], HasCheckedCertificate 16 8 ([[1, 1, 1, 1, 1, 2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [1, 1, 1, 1, 1, 2] [] ∧ LexLE [] [])) h)

private theorem k16t8_cover1162 : ∀ P ∈ pathPatterns 0 0 [1, 1, 1, 1, 1, 2, 1], HasCheckedCertificate 16 8 ([[1, 1, 1, 1, 1, 2, 1]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k16t8p453, Certificates.k16t8p453_check⟩

private theorem k16t8_cover1163 : ∀ P ∈ pathPatterns 1 0 [1, 1, 1, 1, 1, 3], HasCheckedCertificate 16 8 ([[1, 1, 1, 1, 1, 3]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [1, 1, 1, 1, 1, 3] [] ∧ LexLE [] [])) h)

private theorem k16t8_cover1165 : ∀ P ∈ pathPatterns 0 0 [2], HasCheckedCertificate 16 8 ([[1, 1, 1, 1, 2], [2]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k16t8p454, Certificates.k16t8p454_check⟩

private theorem k16t8_cover1164 : ∀ P ∈ pathPatterns 2 2 [1, 1, 1, 1, 2], HasCheckedCertificate 16 8 ([[1, 1, 1, 1, 2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [1, 1, 1, 1, 2] [] ∧ LexLE [] [])) h)
      · intro q
        fin_cases q
        · exact by
            intro h
            exact False.elim ((by decide : ¬ (LexLE [1, 1, 1, 1, 2] [1] ∧ LexLE [1] [1])) h)
        · exact by
            intro _
            exact k16t8_cover1165

private theorem k16t8_cover1166 : ∀ P ∈ pathPatterns 1 1 [1, 1, 1, 1, 2, 1], HasCheckedCertificate 16 8 ([[1, 1, 1, 1, 2, 1]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [1, 1, 1, 1, 2, 1] [] ∧ LexLE [] [])) h)

private theorem k16t8_cover1167 : ∀ P ∈ pathPatterns 0 0 [1, 1, 1, 1, 2, 1, 1], HasCheckedCertificate 16 8 ([[1, 1, 1, 1, 2, 1, 1]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k16t8p455, Certificates.k16t8p455_check⟩

private theorem k16t8_cover1168 : ∀ P ∈ pathPatterns 1 0 [1, 1, 1, 1, 2, 2], HasCheckedCertificate 16 8 ([[1, 1, 1, 1, 2, 2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [1, 1, 1, 1, 2, 2] [] ∧ LexLE [] [])) h)

private theorem k16t8_cover1169 : ∀ P ∈ pathPatterns 2 1 [1, 1, 1, 1, 3], HasCheckedCertificate 16 8 ([[1, 1, 1, 1, 3]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [1, 1, 1, 1, 3] [] ∧ LexLE [] [])) h)
      · intro q
        fin_cases q
        · exact by
            intro h
            exact False.elim ((by decide : ¬ (LexLE [1, 1, 1, 1, 3] [1] ∧ LexLE [1] [1])) h)

private theorem k16t8_cover1170 : ∀ P ∈ pathPatterns 1 0 [1, 1, 1, 1, 3, 1], HasCheckedCertificate 16 8 ([[1, 1, 1, 1, 3, 1]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [1, 1, 1, 1, 3, 1] [] ∧ LexLE [] [])) h)

private theorem k16t8_cover1171 : ∀ P ∈ pathPatterns 2 0 [1, 1, 1, 1, 4], HasCheckedCertificate 16 8 ([[1, 1, 1, 1, 4]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [1, 1, 1, 1, 4] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k16t8_cover1173 : ∀ P ∈ pathPatterns 0 0 [1, 2], HasCheckedCertificate 16 8 ([[1, 1, 1, 2], [1, 2]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k16t8p456, Certificates.k16t8p456_check⟩

private theorem k16t8_cover1174 : ∀ P ∈ pathPatterns 1 1 [2], HasCheckedCertificate 16 8 ([[1, 1, 1, 2], [2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [2] [] ∧ LexLE [] [])) h)

private theorem k16t8_cover1175 : ∀ P ∈ pathPatterns 1 0 [3], HasCheckedCertificate 16 8 ([[1, 1, 1, 2], [3]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [3] [] ∧ LexLE [] [])) h)

private theorem k16t8_cover1172 : ∀ P ∈ pathPatterns 3 3 [1, 1, 1, 2], HasCheckedCertificate 16 8 ([[1, 1, 1, 2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [1, 1, 1, 2] [] ∧ LexLE [] [])) h)
      · intro q
        fin_cases q
        · exact by
            constructor
            · exact by
                intro h
                exact False.elim ((by decide : ¬ (LexLE [1, 1, 1, 2] [1] ∧ LexLE [1] [1])) h)
            · intro q
              fin_cases q
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [1, 1, 1, 2] [1, 1] ∧ LexLE [1, 1] [1, 1])) h)
              · exact by
                  intro _
                  exact k16t8_cover1173
        · exact by
            constructor
            · exact by
                intro _
                exact k16t8_cover1174
            · intro q
              fin_cases q
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [1, 1, 1, 2] [2, 1] ∧ LexLE [2, 1] [1, 2])) h)
        · exact by
            constructor
            · exact by
                intro _
                exact k16t8_cover1175
            · intro q
              exact Fin.elim0 q

private theorem k16t8_cover1177 : ∀ P ∈ pathPatterns 0 0 [2], HasCheckedCertificate 16 8 ([[1, 1, 1, 2, 1], [2]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k16t8p457, Certificates.k16t8p457_check⟩

private theorem k16t8_cover1176 : ∀ P ∈ pathPatterns 2 2 [1, 1, 1, 2, 1], HasCheckedCertificate 16 8 ([[1, 1, 1, 2, 1]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [1, 1, 1, 2, 1] [] ∧ LexLE [] [])) h)
      · intro q
        fin_cases q
        · exact by
            intro h
            exact False.elim ((by decide : ¬ (LexLE [1, 1, 1, 2, 1] [1] ∧ LexLE [1] [1])) h)
        · exact by
            intro _
            exact k16t8_cover1177

private theorem k16t8_cover1178 : ∀ P ∈ pathPatterns 1 1 [1, 1, 1, 2, 1, 1], HasCheckedCertificate 16 8 ([[1, 1, 1, 2, 1, 1]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [1, 1, 1, 2, 1, 1] [] ∧ LexLE [] [])) h)

private theorem k16t8_cover1179 : ∀ P ∈ pathPatterns 0 0 [1, 1, 1, 2, 1, 1, 1], HasCheckedCertificate 16 8 ([[1, 1, 1, 2, 1, 1, 1]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k16t8p458, Certificates.k16t8p458_check⟩

private theorem k16t8_cover1180 : ∀ P ∈ pathPatterns 1 0 [1, 1, 1, 2, 1, 2], HasCheckedCertificate 16 8 ([[1, 1, 1, 2, 1, 2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [1, 1, 1, 2, 1, 2] [] ∧ LexLE [] [])) h)

private theorem k16t8_cover1181 : ∀ P ∈ pathPatterns 2 1 [1, 1, 1, 2, 2], HasCheckedCertificate 16 8 ([[1, 1, 1, 2, 2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [1, 1, 1, 2, 2] [] ∧ LexLE [] [])) h)
      · intro q
        fin_cases q
        · exact by
            intro h
            exact False.elim ((by decide : ¬ (LexLE [1, 1, 1, 2, 2] [1] ∧ LexLE [1] [1])) h)

private theorem k16t8_cover1182 : ∀ P ∈ pathPatterns 1 0 [1, 1, 1, 2, 2, 1], HasCheckedCertificate 16 8 ([[1, 1, 1, 2, 2, 1]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [1, 1, 1, 2, 2, 1] [] ∧ LexLE [] [])) h)

private theorem k16t8_cover1183 : ∀ P ∈ pathPatterns 2 0 [1, 1, 1, 2, 3], HasCheckedCertificate 16 8 ([[1, 1, 1, 2, 3]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [1, 1, 1, 2, 3] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k16t8_cover1185 : ∀ P ∈ pathPatterns 1 0 [2], HasCheckedCertificate 16 8 ([[1, 1, 1, 3], [2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [2] [] ∧ LexLE [] [])) h)

private theorem k16t8_cover1184 : ∀ P ∈ pathPatterns 3 2 [1, 1, 1, 3], HasCheckedCertificate 16 8 ([[1, 1, 1, 3]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [1, 1, 1, 3] [] ∧ LexLE [] [])) h)
      · intro q
        fin_cases q
        · exact by
            constructor
            · exact by
                intro h
                exact False.elim ((by decide : ¬ (LexLE [1, 1, 1, 3] [1] ∧ LexLE [1] [1])) h)
            · intro q
              fin_cases q
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [1, 1, 1, 3] [1, 1] ∧ LexLE [1, 1] [1, 1])) h)
        · exact by
            constructor
            · exact by
                intro _
                exact k16t8_cover1185
            · intro q
              exact Fin.elim0 q

private theorem k16t8_cover1186 : ∀ P ∈ pathPatterns 2 1 [1, 1, 1, 3, 1], HasCheckedCertificate 16 8 ([[1, 1, 1, 3, 1]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [1, 1, 1, 3, 1] [] ∧ LexLE [] [])) h)
      · intro q
        fin_cases q
        · exact by
            intro h
            exact False.elim ((by decide : ¬ (LexLE [1, 1, 1, 3, 1] [1] ∧ LexLE [1] [1])) h)

private theorem k16t8_cover1187 : ∀ P ∈ pathPatterns 1 0 [1, 1, 1, 3, 1, 1], HasCheckedCertificate 16 8 ([[1, 1, 1, 3, 1, 1]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [1, 1, 1, 3, 1, 1] [] ∧ LexLE [] [])) h)

private theorem k16t8_cover1188 : ∀ P ∈ pathPatterns 2 0 [1, 1, 1, 3, 2], HasCheckedCertificate 16 8 ([[1, 1, 1, 3, 2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [1, 1, 1, 3, 2] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k16t8_cover1189 : ∀ P ∈ pathPatterns 3 1 [1, 1, 1, 4], HasCheckedCertificate 16 8 ([[1, 1, 1, 4]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [1, 1, 1, 4] [] ∧ LexLE [] [])) h)
      · intro q
        fin_cases q
        · exact by
            constructor
            · exact by
                intro h
                exact False.elim ((by decide : ¬ (LexLE [1, 1, 1, 4] [1] ∧ LexLE [1] [1])) h)
            · intro q
              exact Fin.elim0 q

private theorem k16t8_cover1190 : ∀ P ∈ pathPatterns 2 0 [1, 1, 1, 4, 1], HasCheckedCertificate 16 8 ([[1, 1, 1, 4, 1]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [1, 1, 1, 4, 1] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k16t8_cover1191 : ∀ P ∈ pathPatterns 3 0 [1, 1, 1, 5], HasCheckedCertificate 16 8 ([[1, 1, 1, 5]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [1, 1, 1, 5] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k16t8_seq1127 : amountSequenceForall 4 5 (fun tail =>
    (LexLE [] ([1, 1, 1] ++ tail) ∧ LexLE ([1, 1, 1] ++ tail) ([1, 1, 1] ++ tail).reverse) →
    ∀ P ∈ pathPatterns (7 - ([1, 1, 1] ++ tail).length) (8 - ([1, 1, 1] ++ tail).sum) ([1, 1, 1] ++ tail),
      HasCheckedCertificate 16 8 ([] ++ (([1, 1, 1] ++ tail) :: P))) :=
by
  constructor
  · exact by
      intro _
      exact k16t8_cover1128
  · intro q
    fin_cases q
    · exact by
        constructor
        · exact by
            intro _
            exact k16t8_cover1148
        · intro q
          fin_cases q
          · exact by
              constructor
              · exact by
                  intro _
                  exact k16t8_cover1155
              · intro q
                fin_cases q
                · exact by
                    constructor
                    · exact by
                        intro _
                        exact k16t8_cover1158
                    · intro q
                      fin_cases q
                      · exact by
                          intro _
                          exact k16t8_cover1159
                      · exact by
                          intro _
                          exact k16t8_cover1160
                · exact by
                    constructor
                    · exact by
                        intro _
                        exact k16t8_cover1161
                    · intro q
                      fin_cases q
                      · exact by
                          intro _
                          exact k16t8_cover1162
                · exact by
                    constructor
                    · exact by
                        intro _
                        exact k16t8_cover1163
                    · intro q
                      exact Fin.elim0 q
          · exact by
              constructor
              · exact by
                  intro _
                  exact k16t8_cover1164
              · intro q
                fin_cases q
                · exact by
                    constructor
                    · exact by
                        intro _
                        exact k16t8_cover1166
                    · intro q
                      fin_cases q
                      · exact by
                          intro _
                          exact k16t8_cover1167
                · exact by
                    constructor
                    · exact by
                        intro _
                        exact k16t8_cover1168
                    · intro q
                      exact Fin.elim0 q
          · exact by
              constructor
              · exact by
                  intro _
                  exact k16t8_cover1169
              · intro q
                fin_cases q
                · exact by
                    constructor
                    · exact by
                        intro _
                        exact k16t8_cover1170
                    · intro q
                      exact Fin.elim0 q
          · exact by
              constructor
              · exact by
                  intro _
                  exact k16t8_cover1171
              · intro q
                exact Fin.elim0 q
    · exact by
        constructor
        · exact by
            intro _
            exact k16t8_cover1172
        · intro q
          fin_cases q
          · exact by
              constructor
              · exact by
                  intro _
                  exact k16t8_cover1176
              · intro q
                fin_cases q
                · exact by
                    constructor
                    · exact by
                        intro _
                        exact k16t8_cover1178
                    · intro q
                      fin_cases q
                      · exact by
                          intro _
                          exact k16t8_cover1179
                · exact by
                    constructor
                    · exact by
                        intro _
                        exact k16t8_cover1180
                    · intro q
                      exact Fin.elim0 q
          · exact by
              constructor
              · exact by
                  intro _
                  exact k16t8_cover1181
              · intro q
                fin_cases q
                · exact by
                    constructor
                    · exact by
                        intro _
                        exact k16t8_cover1182
                    · intro q
                      exact Fin.elim0 q
          · exact by
              constructor
              · exact by
                  intro _
                  exact k16t8_cover1183
              · intro q
                exact Fin.elim0 q
    · exact by
        constructor
        · exact by
            intro _
            exact k16t8_cover1184
        · intro q
          fin_cases q
          · exact by
              constructor
              · exact by
                  intro _
                  exact k16t8_cover1186
              · intro q
                fin_cases q
                · exact by
                    constructor
                    · exact by
                        intro _
                        exact k16t8_cover1187
                    · intro q
                      exact Fin.elim0 q
          · exact by
              constructor
              · exact by
                  intro _
                  exact k16t8_cover1188
              · intro q
                exact Fin.elim0 q
    · exact by
        constructor
        · exact by
            intro _
            exact k16t8_cover1189
        · intro q
          fin_cases q
          · exact by
              constructor
              · exact by
                  intro _
                  exact k16t8_cover1190
              · intro q
                exact Fin.elim0 q
    · exact by
        constructor
        · exact by
            intro _
            exact k16t8_cover1191
        · intro q
          exact Fin.elim0 q

private theorem k16t8_cover1193 : ∀ P ∈ pathPatterns 0 0 [1, 1, 2], HasCheckedCertificate 16 8 ([[1, 1, 2], [1, 1, 2]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k16t8p459, Certificates.k16t8p459_check⟩

private theorem k16t8_cover1194 : ∀ P ∈ pathPatterns 1 1 [1, 2], HasCheckedCertificate 16 8 ([[1, 1, 2], [1, 2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [1, 2] [] ∧ LexLE [] [])) h)

private theorem k16t8_cover1195 : ∀ P ∈ pathPatterns 0 0 [1, 2, 1], HasCheckedCertificate 16 8 ([[1, 1, 2], [1, 2, 1]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k16t8p460, Certificates.k16t8p460_check⟩

private theorem k16t8_cover1196 : ∀ P ∈ pathPatterns 1 0 [1, 3], HasCheckedCertificate 16 8 ([[1, 1, 2], [1, 3]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [1, 3] [] ∧ LexLE [] [])) h)

private theorem k16t8_cover1198 : ∀ P ∈ pathPatterns 0 0 [2], HasCheckedCertificate 16 8 ([[1, 1, 2], [2], [2]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k16t8p461, Certificates.k16t8p461_check⟩

private theorem k16t8_cover1197 : ∀ P ∈ pathPatterns 2 2 [2], HasCheckedCertificate 16 8 ([[1, 1, 2], [2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [2] [] ∧ LexLE [] [])) h)
      · intro q
        fin_cases q
        · exact by
            intro h
            exact False.elim ((by decide : ¬ (LexLE [2] [1] ∧ LexLE [1] [1])) h)
        · exact by
            intro _
            exact k16t8_cover1198

private theorem k16t8_cover1199 : ∀ P ∈ pathPatterns 1 0 [2, 2], HasCheckedCertificate 16 8 ([[1, 1, 2], [2, 2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [2, 2] [] ∧ LexLE [] [])) h)

private theorem k16t8_cover1200 : ∀ P ∈ pathPatterns 2 1 [3], HasCheckedCertificate 16 8 ([[1, 1, 2], [3]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [3] [] ∧ LexLE [] [])) h)
      · intro q
        fin_cases q
        · exact by
            intro h
            exact False.elim ((by decide : ¬ (LexLE [3] [1] ∧ LexLE [1] [1])) h)

private theorem k16t8_cover1201 : ∀ P ∈ pathPatterns 2 0 [4], HasCheckedCertificate 16 8 ([[1, 1, 2], [4]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [4] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k16t8_cover1192 : ∀ P ∈ pathPatterns 4 4 [1, 1, 2], HasCheckedCertificate 16 8 ([[1, 1, 2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [1, 1, 2] [] ∧ LexLE [] [])) h)
      · intro q
        fin_cases q
        · exact by
            constructor
            · exact by
                intro h
                exact False.elim ((by decide : ¬ (LexLE [1, 1, 2] [1] ∧ LexLE [1] [1])) h)
            · intro q
              fin_cases q
              · exact by
                  constructor
                  · exact by
                      intro h
                      exact False.elim ((by decide : ¬ (LexLE [1, 1, 2] [1, 1] ∧ LexLE [1, 1] [1, 1])) h)
                  · intro q
                    fin_cases q
                    · exact by
                        intro h
                        exact False.elim ((by decide : ¬ (LexLE [1, 1, 2] [1, 1, 1] ∧ LexLE [1, 1, 1] [1, 1, 1])) h)
                    · exact by
                        intro _
                        exact k16t8_cover1193
              · exact by
                  constructor
                  · exact by
                      intro _
                      exact k16t8_cover1194
                  · intro q
                    fin_cases q
                    · exact by
                        intro _
                        exact k16t8_cover1195
              · exact by
                  constructor
                  · exact by
                      intro _
                      exact k16t8_cover1196
                  · intro q
                    exact Fin.elim0 q
        · exact by
            constructor
            · exact by
                intro _
                exact k16t8_cover1197
            · intro q
              fin_cases q
              · exact by
                  constructor
                  · exact by
                      intro h
                      exact False.elim ((by decide : ¬ (LexLE [1, 1, 2] [2, 1] ∧ LexLE [2, 1] [1, 2])) h)
                  · intro q
                    fin_cases q
                    · exact by
                        intro h
                        exact False.elim ((by decide : ¬ (LexLE [1, 1, 2] [2, 1, 1] ∧ LexLE [2, 1, 1] [1, 1, 2])) h)
              · exact by
                  constructor
                  · exact by
                      intro _
                      exact k16t8_cover1199
                  · intro q
                    exact Fin.elim0 q
        · exact by
            constructor
            · exact by
                intro _
                exact k16t8_cover1200
            · intro q
              fin_cases q
              · exact by
                  constructor
                  · exact by
                      intro h
                      exact False.elim ((by decide : ¬ (LexLE [1, 1, 2] [3, 1] ∧ LexLE [3, 1] [1, 3])) h)
                  · intro q
                    exact Fin.elim0 q
        · exact by
            constructor
            · exact by
                intro _
                exact k16t8_cover1201
            · intro q
              exact Fin.elim0 q

private theorem k16t8_cover1203 : ∀ P ∈ pathPatterns 0 0 [1, 2], HasCheckedCertificate 16 8 ([[1, 1, 2, 1], [1, 2]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k16t8p462, Certificates.k16t8p462_check⟩

private theorem k16t8_cover1204 : ∀ P ∈ pathPatterns 1 1 [2], HasCheckedCertificate 16 8 ([[1, 1, 2, 1], [2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [2] [] ∧ LexLE [] [])) h)

private theorem k16t8_cover1205 : ∀ P ∈ pathPatterns 1 0 [3], HasCheckedCertificate 16 8 ([[1, 1, 2, 1], [3]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [3] [] ∧ LexLE [] [])) h)

private theorem k16t8_cover1202 : ∀ P ∈ pathPatterns 3 3 [1, 1, 2, 1], HasCheckedCertificate 16 8 ([[1, 1, 2, 1]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [1, 1, 2, 1] [] ∧ LexLE [] [])) h)
      · intro q
        fin_cases q
        · exact by
            constructor
            · exact by
                intro h
                exact False.elim ((by decide : ¬ (LexLE [1, 1, 2, 1] [1] ∧ LexLE [1] [1])) h)
            · intro q
              fin_cases q
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [1, 1, 2, 1] [1, 1] ∧ LexLE [1, 1] [1, 1])) h)
              · exact by
                  intro _
                  exact k16t8_cover1203
        · exact by
            constructor
            · exact by
                intro _
                exact k16t8_cover1204
            · intro q
              fin_cases q
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [1, 1, 2, 1] [2, 1] ∧ LexLE [2, 1] [1, 2])) h)
        · exact by
            constructor
            · exact by
                intro _
                exact k16t8_cover1205
            · intro q
              exact Fin.elim0 q

private theorem k16t8_cover1207 : ∀ P ∈ pathPatterns 0 0 [2], HasCheckedCertificate 16 8 ([[1, 1, 2, 1, 1], [2]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k16t8p463, Certificates.k16t8p463_check⟩

private theorem k16t8_cover1206 : ∀ P ∈ pathPatterns 2 2 [1, 1, 2, 1, 1], HasCheckedCertificate 16 8 ([[1, 1, 2, 1, 1]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [1, 1, 2, 1, 1] [] ∧ LexLE [] [])) h)
      · intro q
        fin_cases q
        · exact by
            intro h
            exact False.elim ((by decide : ¬ (LexLE [1, 1, 2, 1, 1] [1] ∧ LexLE [1] [1])) h)
        · exact by
            intro _
            exact k16t8_cover1207

private theorem k16t8_cover1208 : ∀ P ∈ pathPatterns 1 0 [1, 1, 2, 1, 1, 2], HasCheckedCertificate 16 8 ([[1, 1, 2, 1, 1, 2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [1, 1, 2, 1, 1, 2] [] ∧ LexLE [] [])) h)

private theorem k16t8_cover1209 : ∀ P ∈ pathPatterns 2 1 [1, 1, 2, 1, 2], HasCheckedCertificate 16 8 ([[1, 1, 2, 1, 2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [1, 1, 2, 1, 2] [] ∧ LexLE [] [])) h)
      · intro q
        fin_cases q
        · exact by
            intro h
            exact False.elim ((by decide : ¬ (LexLE [1, 1, 2, 1, 2] [1] ∧ LexLE [1] [1])) h)

private theorem k16t8_cover1210 : ∀ P ∈ pathPatterns 1 0 [1, 1, 2, 1, 2, 1], HasCheckedCertificate 16 8 ([[1, 1, 2, 1, 2, 1]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [1, 1, 2, 1, 2, 1] [] ∧ LexLE [] [])) h)

private theorem k16t8_cover1211 : ∀ P ∈ pathPatterns 2 0 [1, 1, 2, 1, 3], HasCheckedCertificate 16 8 ([[1, 1, 2, 1, 3]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [1, 1, 2, 1, 3] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k16t8_cover1213 : ∀ P ∈ pathPatterns 1 0 [2], HasCheckedCertificate 16 8 ([[1, 1, 2, 2], [2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [2] [] ∧ LexLE [] [])) h)

private theorem k16t8_cover1212 : ∀ P ∈ pathPatterns 3 2 [1, 1, 2, 2], HasCheckedCertificate 16 8 ([[1, 1, 2, 2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [1, 1, 2, 2] [] ∧ LexLE [] [])) h)
      · intro q
        fin_cases q
        · exact by
            constructor
            · exact by
                intro h
                exact False.elim ((by decide : ¬ (LexLE [1, 1, 2, 2] [1] ∧ LexLE [1] [1])) h)
            · intro q
              fin_cases q
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [1, 1, 2, 2] [1, 1] ∧ LexLE [1, 1] [1, 1])) h)
        · exact by
            constructor
            · exact by
                intro _
                exact k16t8_cover1213
            · intro q
              exact Fin.elim0 q

private theorem k16t8_cover1214 : ∀ P ∈ pathPatterns 2 1 [1, 1, 2, 2, 1], HasCheckedCertificate 16 8 ([[1, 1, 2, 2, 1]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [1, 1, 2, 2, 1] [] ∧ LexLE [] [])) h)
      · intro q
        fin_cases q
        · exact by
            intro h
            exact False.elim ((by decide : ¬ (LexLE [1, 1, 2, 2, 1] [1] ∧ LexLE [1] [1])) h)

private theorem k16t8_cover1215 : ∀ P ∈ pathPatterns 1 0 [1, 1, 2, 2, 1, 1], HasCheckedCertificate 16 8 ([[1, 1, 2, 2, 1, 1]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [1, 1, 2, 2, 1, 1] [] ∧ LexLE [] [])) h)

private theorem k16t8_cover1216 : ∀ P ∈ pathPatterns 2 0 [1, 1, 2, 2, 2], HasCheckedCertificate 16 8 ([[1, 1, 2, 2, 2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [1, 1, 2, 2, 2] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k16t8_cover1217 : ∀ P ∈ pathPatterns 3 1 [1, 1, 2, 3], HasCheckedCertificate 16 8 ([[1, 1, 2, 3]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [1, 1, 2, 3] [] ∧ LexLE [] [])) h)
      · intro q
        fin_cases q
        · exact by
            constructor
            · exact by
                intro h
                exact False.elim ((by decide : ¬ (LexLE [1, 1, 2, 3] [1] ∧ LexLE [1] [1])) h)
            · intro q
              exact Fin.elim0 q

private theorem k16t8_cover1218 : ∀ P ∈ pathPatterns 2 0 [1, 1, 2, 3, 1], HasCheckedCertificate 16 8 ([[1, 1, 2, 3, 1]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [1, 1, 2, 3, 1] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k16t8_cover1219 : ∀ P ∈ pathPatterns 3 0 [1, 1, 2, 4], HasCheckedCertificate 16 8 ([[1, 1, 2, 4]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [1, 1, 2, 4] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k16t8_cover1221 : ∀ P ∈ pathPatterns 1 0 [1, 2], HasCheckedCertificate 16 8 ([[1, 1, 3], [1, 2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [1, 2] [] ∧ LexLE [] [])) h)

private theorem k16t8_cover1222 : ∀ P ∈ pathPatterns 2 1 [2], HasCheckedCertificate 16 8 ([[1, 1, 3], [2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [2] [] ∧ LexLE [] [])) h)
      · intro q
        fin_cases q
        · exact by
            intro h
            exact False.elim ((by decide : ¬ (LexLE [2] [1] ∧ LexLE [1] [1])) h)

private theorem k16t8_cover1223 : ∀ P ∈ pathPatterns 2 0 [3], HasCheckedCertificate 16 8 ([[1, 1, 3], [3]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [3] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k16t8_cover1220 : ∀ P ∈ pathPatterns 4 3 [1, 1, 3], HasCheckedCertificate 16 8 ([[1, 1, 3]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [1, 1, 3] [] ∧ LexLE [] [])) h)
      · intro q
        fin_cases q
        · exact by
            constructor
            · exact by
                intro h
                exact False.elim ((by decide : ¬ (LexLE [1, 1, 3] [1] ∧ LexLE [1] [1])) h)
            · intro q
              fin_cases q
              · exact by
                  constructor
                  · exact by
                      intro h
                      exact False.elim ((by decide : ¬ (LexLE [1, 1, 3] [1, 1] ∧ LexLE [1, 1] [1, 1])) h)
                  · intro q
                    fin_cases q
                    · exact by
                        intro h
                        exact False.elim ((by decide : ¬ (LexLE [1, 1, 3] [1, 1, 1] ∧ LexLE [1, 1, 1] [1, 1, 1])) h)
              · exact by
                  constructor
                  · exact by
                      intro _
                      exact k16t8_cover1221
                  · intro q
                    exact Fin.elim0 q
        · exact by
            constructor
            · exact by
                intro _
                exact k16t8_cover1222
            · intro q
              fin_cases q
              · exact by
                  constructor
                  · exact by
                      intro h
                      exact False.elim ((by decide : ¬ (LexLE [1, 1, 3] [2, 1] ∧ LexLE [2, 1] [1, 2])) h)
                  · intro q
                    exact Fin.elim0 q
        · exact by
            constructor
            · exact by
                intro _
                exact k16t8_cover1223
            · intro q
              exact Fin.elim0 q

private theorem k16t8_cover1225 : ∀ P ∈ pathPatterns 1 0 [2], HasCheckedCertificate 16 8 ([[1, 1, 3, 1], [2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [2] [] ∧ LexLE [] [])) h)

private theorem k16t8_cover1224 : ∀ P ∈ pathPatterns 3 2 [1, 1, 3, 1], HasCheckedCertificate 16 8 ([[1, 1, 3, 1]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [1, 1, 3, 1] [] ∧ LexLE [] [])) h)
      · intro q
        fin_cases q
        · exact by
            constructor
            · exact by
                intro h
                exact False.elim ((by decide : ¬ (LexLE [1, 1, 3, 1] [1] ∧ LexLE [1] [1])) h)
            · intro q
              fin_cases q
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [1, 1, 3, 1] [1, 1] ∧ LexLE [1, 1] [1, 1])) h)
        · exact by
            constructor
            · exact by
                intro _
                exact k16t8_cover1225
            · intro q
              exact Fin.elim0 q

private theorem k16t8_cover1226 : ∀ P ∈ pathPatterns 2 1 [1, 1, 3, 1, 1], HasCheckedCertificate 16 8 ([[1, 1, 3, 1, 1]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [1, 1, 3, 1, 1] [] ∧ LexLE [] [])) h)
      · intro q
        fin_cases q
        · exact by
            intro h
            exact False.elim ((by decide : ¬ (LexLE [1, 1, 3, 1, 1] [1] ∧ LexLE [1] [1])) h)

private theorem k16t8_cover1227 : ∀ P ∈ pathPatterns 2 0 [1, 1, 3, 1, 2], HasCheckedCertificate 16 8 ([[1, 1, 3, 1, 2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [1, 1, 3, 1, 2] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k16t8_cover1228 : ∀ P ∈ pathPatterns 3 1 [1, 1, 3, 2], HasCheckedCertificate 16 8 ([[1, 1, 3, 2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [1, 1, 3, 2] [] ∧ LexLE [] [])) h)
      · intro q
        fin_cases q
        · exact by
            constructor
            · exact by
                intro h
                exact False.elim ((by decide : ¬ (LexLE [1, 1, 3, 2] [1] ∧ LexLE [1] [1])) h)
            · intro q
              exact Fin.elim0 q

private theorem k16t8_cover1229 : ∀ P ∈ pathPatterns 2 0 [1, 1, 3, 2, 1], HasCheckedCertificate 16 8 ([[1, 1, 3, 2, 1]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [1, 1, 3, 2, 1] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k16t8_cover1230 : ∀ P ∈ pathPatterns 3 0 [1, 1, 3, 3], HasCheckedCertificate 16 8 ([[1, 1, 3, 3]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [1, 1, 3, 3] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k16t8_cover1232 : ∀ P ∈ pathPatterns 2 0 [2], HasCheckedCertificate 16 8 ([[1, 1, 4], [2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [2] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k16t8_cover1231 : ∀ P ∈ pathPatterns 4 2 [1, 1, 4], HasCheckedCertificate 16 8 ([[1, 1, 4]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [1, 1, 4] [] ∧ LexLE [] [])) h)
      · intro q
        fin_cases q
        · exact by
            constructor
            · exact by
                intro h
                exact False.elim ((by decide : ¬ (LexLE [1, 1, 4] [1] ∧ LexLE [1] [1])) h)
            · intro q
              fin_cases q
              · exact by
                  constructor
                  · exact by
                      intro h
                      exact False.elim ((by decide : ¬ (LexLE [1, 1, 4] [1, 1] ∧ LexLE [1, 1] [1, 1])) h)
                  · intro q
                    exact Fin.elim0 q
        · exact by
            constructor
            · exact by
                intro _
                exact k16t8_cover1232
            · intro q
              exact Fin.elim0 q

private theorem k16t8_cover1233 : ∀ P ∈ pathPatterns 3 1 [1, 1, 4, 1], HasCheckedCertificate 16 8 ([[1, 1, 4, 1]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [1, 1, 4, 1] [] ∧ LexLE [] [])) h)
      · intro q
        fin_cases q
        · exact by
            constructor
            · exact by
                intro h
                exact False.elim ((by decide : ¬ (LexLE [1, 1, 4, 1] [1] ∧ LexLE [1] [1])) h)
            · intro q
              exact Fin.elim0 q

private theorem k16t8_cover1234 : ∀ P ∈ pathPatterns 2 0 [1, 1, 4, 1, 1], HasCheckedCertificate 16 8 ([[1, 1, 4, 1, 1]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [1, 1, 4, 1, 1] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k16t8_cover1235 : ∀ P ∈ pathPatterns 3 0 [1, 1, 4, 2], HasCheckedCertificate 16 8 ([[1, 1, 4, 2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [1, 1, 4, 2] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k16t8_cover1236 : ∀ P ∈ pathPatterns 4 1 [1, 1, 5], HasCheckedCertificate 16 8 ([[1, 1, 5]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [1, 1, 5] [] ∧ LexLE [] [])) h)
      · intro q
        fin_cases q
        · exact by
            constructor
            · exact by
                intro h
                exact False.elim ((by decide : ¬ (LexLE [1, 1, 5] [1] ∧ LexLE [1] [1])) h)
            · intro q
              exact Fin.elim0 q

private theorem k16t8_cover1237 : ∀ P ∈ pathPatterns 3 0 [1, 1, 5, 1], HasCheckedCertificate 16 8 ([[1, 1, 5, 1]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [1, 1, 5, 1] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k16t8_cover1238 : ∀ P ∈ pathPatterns 4 0 [1, 1, 6], HasCheckedCertificate 16 8 ([[1, 1, 6]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [1, 1, 6] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k16t8_seq1076 : amountSequenceForall 5 6 (fun tail =>
    (LexLE [] ([1, 1] ++ tail) ∧ LexLE ([1, 1] ++ tail) ([1, 1] ++ tail).reverse) →
    ∀ P ∈ pathPatterns (7 - ([1, 1] ++ tail).length) (8 - ([1, 1] ++ tail).sum) ([1, 1] ++ tail),
      HasCheckedCertificate 16 8 ([] ++ (([1, 1] ++ tail) :: P))) :=
by
  constructor
  · exact by
      intro _
      exact k16t8_cover1077
  · intro q
    fin_cases q
    · exact k16t8_seq1127

    · exact by
        constructor
        · exact by
            intro _
            exact k16t8_cover1192
        · intro q
          fin_cases q
          · exact by
              constructor
              · exact by
                  intro _
                  exact k16t8_cover1202
              · intro q
                fin_cases q
                · exact by
                    constructor
                    · exact by
                        intro _
                        exact k16t8_cover1206
                    · intro q
                      fin_cases q
                      · exact by
                          constructor
                          · exact by
                              intro h
                              exact False.elim ((by decide : ¬ (LexLE [] [1, 1, 2, 1, 1, 1] ∧ LexLE [1, 1, 2, 1, 1, 1] [1, 1, 1, 2, 1, 1])) h)
                          · intro q
                            fin_cases q
                            · exact by
                                intro h
                                exact False.elim ((by decide : ¬ (LexLE [] [1, 1, 2, 1, 1, 1, 1] ∧ LexLE [1, 1, 2, 1, 1, 1, 1] [1, 1, 1, 1, 2, 1, 1])) h)
                      · exact by
                          constructor
                          · exact by
                              intro _
                              exact k16t8_cover1208
                          · intro q
                            exact Fin.elim0 q
                · exact by
                    constructor
                    · exact by
                        intro _
                        exact k16t8_cover1209
                    · intro q
                      fin_cases q
                      · exact by
                          constructor
                          · exact by
                              intro _
                              exact k16t8_cover1210
                          · intro q
                            exact Fin.elim0 q
                · exact by
                    constructor
                    · exact by
                        intro _
                        exact k16t8_cover1211
                    · intro q
                      exact Fin.elim0 q
          · exact by
              constructor
              · exact by
                  intro _
                  exact k16t8_cover1212
              · intro q
                fin_cases q
                · exact by
                    constructor
                    · exact by
                        intro _
                        exact k16t8_cover1214
                    · intro q
                      fin_cases q
                      · exact by
                          constructor
                          · exact by
                              intro _
                              exact k16t8_cover1215
                          · intro q
                            exact Fin.elim0 q
                · exact by
                    constructor
                    · exact by
                        intro _
                        exact k16t8_cover1216
                    · intro q
                      exact Fin.elim0 q
          · exact by
              constructor
              · exact by
                  intro _
                  exact k16t8_cover1217
              · intro q
                fin_cases q
                · exact by
                    constructor
                    · exact by
                        intro _
                        exact k16t8_cover1218
                    · intro q
                      exact Fin.elim0 q
          · exact by
              constructor
              · exact by
                  intro _
                  exact k16t8_cover1219
              · intro q
                exact Fin.elim0 q
    · exact by
        constructor
        · exact by
            intro _
            exact k16t8_cover1220
        · intro q
          fin_cases q
          · exact by
              constructor
              · exact by
                  intro _
                  exact k16t8_cover1224
              · intro q
                fin_cases q
                · exact by
                    constructor
                    · exact by
                        intro _
                        exact k16t8_cover1226
                    · intro q
                      fin_cases q
                      · exact by
                          constructor
                          · exact by
                              intro h
                              exact False.elim ((by decide : ¬ (LexLE [] [1, 1, 3, 1, 1, 1] ∧ LexLE [1, 1, 3, 1, 1, 1] [1, 1, 1, 3, 1, 1])) h)
                          · intro q
                            exact Fin.elim0 q
                · exact by
                    constructor
                    · exact by
                        intro _
                        exact k16t8_cover1227
                    · intro q
                      exact Fin.elim0 q
          · exact by
              constructor
              · exact by
                  intro _
                  exact k16t8_cover1228
              · intro q
                fin_cases q
                · exact by
                    constructor
                    · exact by
                        intro _
                        exact k16t8_cover1229
                    · intro q
                      exact Fin.elim0 q
          · exact by
              constructor
              · exact by
                  intro _
                  exact k16t8_cover1230
              · intro q
                exact Fin.elim0 q
    · exact by
        constructor
        · exact by
            intro _
            exact k16t8_cover1231
        · intro q
          fin_cases q
          · exact by
              constructor
              · exact by
                  intro _
                  exact k16t8_cover1233
              · intro q
                fin_cases q
                · exact by
                    constructor
                    · exact by
                        intro _
                        exact k16t8_cover1234
                    · intro q
                      exact Fin.elim0 q
          · exact by
              constructor
              · exact by
                  intro _
                  exact k16t8_cover1235
              · intro q
                exact Fin.elim0 q
    · exact by
        constructor
        · exact by
            intro _
            exact k16t8_cover1236
        · intro q
          fin_cases q
          · exact by
              constructor
              · exact by
                  intro _
                  exact k16t8_cover1237
              · intro q
                exact Fin.elim0 q
    · exact by
        constructor
        · exact by
            intro _
            exact k16t8_cover1238
        · intro q
          exact Fin.elim0 q

private theorem k16t8_cover1243 : ∀ P ∈ pathPatterns 0 0 [2], HasCheckedCertificate 16 8 ([[1, 2], [1, 2], [2]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k16t8p464, Certificates.k16t8p464_check⟩

private theorem k16t8_cover1242 : ∀ P ∈ pathPatterns 2 2 [1, 2], HasCheckedCertificate 16 8 ([[1, 2], [1, 2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [1, 2] [] ∧ LexLE [] [])) h)
      · intro q
        fin_cases q
        · exact by
            intro h
            exact False.elim ((by decide : ¬ (LexLE [1, 2] [1] ∧ LexLE [1] [1])) h)
        · exact by
            intro _
            exact k16t8_cover1243

private theorem k16t8_cover1244 : ∀ P ∈ pathPatterns 1 1 [1, 2, 1], HasCheckedCertificate 16 8 ([[1, 2], [1, 2, 1]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [1, 2, 1] [] ∧ LexLE [] [])) h)

private theorem k16t8_cover1245 : ∀ P ∈ pathPatterns 1 0 [1, 2, 2], HasCheckedCertificate 16 8 ([[1, 2], [1, 2, 2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [1, 2, 2] [] ∧ LexLE [] [])) h)

private theorem k16t8_cover1246 : ∀ P ∈ pathPatterns 2 1 [1, 3], HasCheckedCertificate 16 8 ([[1, 2], [1, 3]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [1, 3] [] ∧ LexLE [] [])) h)
      · intro q
        fin_cases q
        · exact by
            intro h
            exact False.elim ((by decide : ¬ (LexLE [1, 3] [1] ∧ LexLE [1] [1])) h)

private theorem k16t8_cover1247 : ∀ P ∈ pathPatterns 1 0 [1, 3, 1], HasCheckedCertificate 16 8 ([[1, 2], [1, 3, 1]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [1, 3, 1] [] ∧ LexLE [] [])) h)

private theorem k16t8_cover1248 : ∀ P ∈ pathPatterns 2 0 [1, 4], HasCheckedCertificate 16 8 ([[1, 2], [1, 4]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [1, 4] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k16t8_cover1250 : ∀ P ∈ pathPatterns 1 1 [2], HasCheckedCertificate 16 8 ([[1, 2], [2], [2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [2] [] ∧ LexLE [] [])) h)

private theorem k16t8_cover1251 : ∀ P ∈ pathPatterns 1 0 [3], HasCheckedCertificate 16 8 ([[1, 2], [2], [3]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [3] [] ∧ LexLE [] [])) h)

private theorem k16t8_cover1249 : ∀ P ∈ pathPatterns 3 3 [2], HasCheckedCertificate 16 8 ([[1, 2], [2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [2] [] ∧ LexLE [] [])) h)
      · intro q
        fin_cases q
        · exact by
            constructor
            · exact by
                intro h
                exact False.elim ((by decide : ¬ (LexLE [2] [1] ∧ LexLE [1] [1])) h)
            · intro q
              fin_cases q
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [2] [1, 1] ∧ LexLE [1, 1] [1, 1])) h)
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [2] [1, 2] ∧ LexLE [1, 2] [2, 1])) h)
        · exact by
            constructor
            · exact by
                intro _
                exact k16t8_cover1250
            · intro q
              fin_cases q
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [2] [2, 1] ∧ LexLE [2, 1] [1, 2])) h)
        · exact by
            constructor
            · exact by
                intro _
                exact k16t8_cover1251
            · intro q
              exact Fin.elim0 q

private theorem k16t8_cover1252 : ∀ P ∈ pathPatterns 1 0 [2, 1, 2], HasCheckedCertificate 16 8 ([[1, 2], [2, 1, 2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [2, 1, 2] [] ∧ LexLE [] [])) h)

private theorem k16t8_cover1253 : ∀ P ∈ pathPatterns 2 1 [2, 2], HasCheckedCertificate 16 8 ([[1, 2], [2, 2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [2, 2] [] ∧ LexLE [] [])) h)
      · intro q
        fin_cases q
        · exact by
            intro h
            exact False.elim ((by decide : ¬ (LexLE [2, 2] [1] ∧ LexLE [1] [1])) h)

private theorem k16t8_cover1254 : ∀ P ∈ pathPatterns 2 0 [2, 3], HasCheckedCertificate 16 8 ([[1, 2], [2, 3]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [2, 3] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k16t8_cover1255 : ∀ P ∈ pathPatterns 3 2 [3], HasCheckedCertificate 16 8 ([[1, 2], [3]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [3] [] ∧ LexLE [] [])) h)
      · intro q
        fin_cases q
        · exact by
            constructor
            · exact by
                intro h
                exact False.elim ((by decide : ¬ (LexLE [3] [1] ∧ LexLE [1] [1])) h)
            · intro q
              fin_cases q
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [3] [1, 1] ∧ LexLE [1, 1] [1, 1])) h)
        · exact by
            constructor
            · exact by
                intro h
                exact False.elim ((by decide : ¬ (LexLE [3] [2] ∧ LexLE [2] [2])) h)
            · intro q
              exact Fin.elim0 q

private theorem k16t8_cover1256 : ∀ P ∈ pathPatterns 3 1 [4], HasCheckedCertificate 16 8 ([[1, 2], [4]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [4] [] ∧ LexLE [] [])) h)
      · intro q
        fin_cases q
        · exact by
            constructor
            · exact by
                intro h
                exact False.elim ((by decide : ¬ (LexLE [4] [1] ∧ LexLE [1] [1])) h)
            · intro q
              exact Fin.elim0 q

private theorem k16t8_cover1257 : ∀ P ∈ pathPatterns 3 0 [5], HasCheckedCertificate 16 8 ([[1, 2], [5]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [5] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k16t8_seq1241 : amountSequenceForall 4 5 (fun tail =>
    (LexLE [1, 2] ([] ++ tail) ∧ LexLE ([] ++ tail) ([] ++ tail).reverse) →
    ∀ P ∈ pathPatterns (4 - ([] ++ tail).length) (5 - ([] ++ tail).sum) ([] ++ tail),
      HasCheckedCertificate 16 8 ([[1, 2]] ++ (([] ++ tail) :: P))) :=
by
  constructor
  · exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [1, 2] [] ∧ LexLE [] [])) h)
  · intro q
    fin_cases q
    · exact by
        constructor
        · exact by
            intro h
            exact False.elim ((by decide : ¬ (LexLE [1, 2] [1] ∧ LexLE [1] [1])) h)
        · intro q
          fin_cases q
          · exact by
              constructor
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [1, 2] [1, 1] ∧ LexLE [1, 1] [1, 1])) h)
              · intro q
                fin_cases q
                · exact by
                    constructor
                    · exact by
                        intro h
                        exact False.elim ((by decide : ¬ (LexLE [1, 2] [1, 1, 1] ∧ LexLE [1, 1, 1] [1, 1, 1])) h)
                    · intro q
                      fin_cases q
                      · exact by
                          intro h
                          exact False.elim ((by decide : ¬ (LexLE [1, 2] [1, 1, 1, 1] ∧ LexLE [1, 1, 1, 1] [1, 1, 1, 1])) h)
                      · exact by
                          intro h
                          exact False.elim ((by decide : ¬ (LexLE [1, 2] [1, 1, 1, 2] ∧ LexLE [1, 1, 1, 2] [2, 1, 1, 1])) h)
                · exact by
                    constructor
                    · exact by
                        intro h
                        exact False.elim ((by decide : ¬ (LexLE [1, 2] [1, 1, 2] ∧ LexLE [1, 1, 2] [2, 1, 1])) h)
                    · intro q
                      fin_cases q
                      · exact by
                          intro h
                          exact False.elim ((by decide : ¬ (LexLE [1, 2] [1, 1, 2, 1] ∧ LexLE [1, 1, 2, 1] [1, 2, 1, 1])) h)
                · exact by
                    constructor
                    · exact by
                        intro h
                        exact False.elim ((by decide : ¬ (LexLE [1, 2] [1, 1, 3] ∧ LexLE [1, 1, 3] [3, 1, 1])) h)
                    · intro q
                      exact Fin.elim0 q
          · exact by
              constructor
              · exact by
                  intro _
                  exact k16t8_cover1242
              · intro q
                fin_cases q
                · exact by
                    constructor
                    · exact by
                        intro _
                        exact k16t8_cover1244
                    · intro q
                      fin_cases q
                      · exact by
                          intro h
                          exact False.elim ((by decide : ¬ (LexLE [1, 2] [1, 2, 1, 1] ∧ LexLE [1, 2, 1, 1] [1, 1, 2, 1])) h)
                · exact by
                    constructor
                    · exact by
                        intro _
                        exact k16t8_cover1245
                    · intro q
                      exact Fin.elim0 q
          · exact by
              constructor
              · exact by
                  intro _
                  exact k16t8_cover1246
              · intro q
                fin_cases q
                · exact by
                    constructor
                    · exact by
                        intro _
                        exact k16t8_cover1247
                    · intro q
                      exact Fin.elim0 q
          · exact by
              constructor
              · exact by
                  intro _
                  exact k16t8_cover1248
              · intro q
                exact Fin.elim0 q
    · exact by
        constructor
        · exact by
            intro _
            exact k16t8_cover1249
        · intro q
          fin_cases q
          · exact by
              constructor
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [1, 2] [2, 1] ∧ LexLE [2, 1] [1, 2])) h)
              · intro q
                fin_cases q
                · exact by
                    constructor
                    · exact by
                        intro h
                        exact False.elim ((by decide : ¬ (LexLE [1, 2] [2, 1, 1] ∧ LexLE [2, 1, 1] [1, 1, 2])) h)
                    · intro q
                      fin_cases q
                      · exact by
                          intro h
                          exact False.elim ((by decide : ¬ (LexLE [1, 2] [2, 1, 1, 1] ∧ LexLE [2, 1, 1, 1] [1, 1, 1, 2])) h)
                · exact by
                    constructor
                    · exact by
                        intro _
                        exact k16t8_cover1252
                    · intro q
                      exact Fin.elim0 q
          · exact by
              constructor
              · exact by
                  intro _
                  exact k16t8_cover1253
              · intro q
                fin_cases q
                · exact by
                    constructor
                    · exact by
                        intro h
                        exact False.elim ((by decide : ¬ (LexLE [1, 2] [2, 2, 1] ∧ LexLE [2, 2, 1] [1, 2, 2])) h)
                    · intro q
                      exact Fin.elim0 q
          · exact by
              constructor
              · exact by
                  intro _
                  exact k16t8_cover1254
              · intro q
                exact Fin.elim0 q
    · exact by
        constructor
        · exact by
            intro _
            exact k16t8_cover1255
        · intro q
          fin_cases q
          · exact by
              constructor
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [1, 2] [3, 1] ∧ LexLE [3, 1] [1, 3])) h)
              · intro q
                fin_cases q
                · exact by
                    constructor
                    · exact by
                        intro h
                        exact False.elim ((by decide : ¬ (LexLE [1, 2] [3, 1, 1] ∧ LexLE [3, 1, 1] [1, 1, 3])) h)
                    · intro q
                      exact Fin.elim0 q
          · exact by
              constructor
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [1, 2] [3, 2] ∧ LexLE [3, 2] [2, 3])) h)
              · intro q
                exact Fin.elim0 q
    · exact by
        constructor
        · exact by
            intro _
            exact k16t8_cover1256
        · intro q
          fin_cases q
          · exact by
              constructor
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [1, 2] [4, 1] ∧ LexLE [4, 1] [1, 4])) h)
              · intro q
                exact Fin.elim0 q
    · exact by
        constructor
        · exact by
            intro _
            exact k16t8_cover1257
        · intro q
          exact Fin.elim0 q

private theorem k16t8_cover1240 : ∀ P ∈ pathPatterns 5 5 [1, 2], HasCheckedCertificate 16 8 ([[1, 2]] ++ P) := by
  apply pathPatterns_forall_step
  exact k16t8_seq1241


private theorem k16t8_cover1259 : ∀ P ∈ pathPatterns 0 0 [1, 2, 1], HasCheckedCertificate 16 8 ([[1, 2, 1], [1, 2, 1]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k16t8p465, Certificates.k16t8p465_check⟩

private theorem k16t8_cover1260 : ∀ P ∈ pathPatterns 1 0 [1, 3], HasCheckedCertificate 16 8 ([[1, 2, 1], [1, 3]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [1, 3] [] ∧ LexLE [] [])) h)

private theorem k16t8_cover1262 : ∀ P ∈ pathPatterns 0 0 [2], HasCheckedCertificate 16 8 ([[1, 2, 1], [2], [2]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k16t8p466, Certificates.k16t8p466_check⟩

private theorem k16t8_cover1261 : ∀ P ∈ pathPatterns 2 2 [2], HasCheckedCertificate 16 8 ([[1, 2, 1], [2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [2] [] ∧ LexLE [] [])) h)
      · intro q
        fin_cases q
        · exact by
            intro h
            exact False.elim ((by decide : ¬ (LexLE [2] [1] ∧ LexLE [1] [1])) h)
        · exact by
            intro _
            exact k16t8_cover1262

private theorem k16t8_cover1263 : ∀ P ∈ pathPatterns 1 0 [2, 2], HasCheckedCertificate 16 8 ([[1, 2, 1], [2, 2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [2, 2] [] ∧ LexLE [] [])) h)

private theorem k16t8_cover1264 : ∀ P ∈ pathPatterns 2 1 [3], HasCheckedCertificate 16 8 ([[1, 2, 1], [3]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [3] [] ∧ LexLE [] [])) h)
      · intro q
        fin_cases q
        · exact by
            intro h
            exact False.elim ((by decide : ¬ (LexLE [3] [1] ∧ LexLE [1] [1])) h)

private theorem k16t8_cover1265 : ∀ P ∈ pathPatterns 2 0 [4], HasCheckedCertificate 16 8 ([[1, 2, 1], [4]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [4] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k16t8_cover1258 : ∀ P ∈ pathPatterns 4 4 [1, 2, 1], HasCheckedCertificate 16 8 ([[1, 2, 1]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [1, 2, 1] [] ∧ LexLE [] [])) h)
      · intro q
        fin_cases q
        · exact by
            constructor
            · exact by
                intro h
                exact False.elim ((by decide : ¬ (LexLE [1, 2, 1] [1] ∧ LexLE [1] [1])) h)
            · intro q
              fin_cases q
              · exact by
                  constructor
                  · exact by
                      intro h
                      exact False.elim ((by decide : ¬ (LexLE [1, 2, 1] [1, 1] ∧ LexLE [1, 1] [1, 1])) h)
                  · intro q
                    fin_cases q
                    · exact by
                        intro h
                        exact False.elim ((by decide : ¬ (LexLE [1, 2, 1] [1, 1, 1] ∧ LexLE [1, 1, 1] [1, 1, 1])) h)
                    · exact by
                        intro h
                        exact False.elim ((by decide : ¬ (LexLE [1, 2, 1] [1, 1, 2] ∧ LexLE [1, 1, 2] [2, 1, 1])) h)
              · exact by
                  constructor
                  · exact by
                      intro h
                      exact False.elim ((by decide : ¬ (LexLE [1, 2, 1] [1, 2] ∧ LexLE [1, 2] [2, 1])) h)
                  · intro q
                    fin_cases q
                    · exact by
                        intro _
                        exact k16t8_cover1259
              · exact by
                  constructor
                  · exact by
                      intro _
                      exact k16t8_cover1260
                  · intro q
                    exact Fin.elim0 q
        · exact by
            constructor
            · exact by
                intro _
                exact k16t8_cover1261
            · intro q
              fin_cases q
              · exact by
                  constructor
                  · exact by
                      intro h
                      exact False.elim ((by decide : ¬ (LexLE [1, 2, 1] [2, 1] ∧ LexLE [2, 1] [1, 2])) h)
                  · intro q
                    fin_cases q
                    · exact by
                        intro h
                        exact False.elim ((by decide : ¬ (LexLE [1, 2, 1] [2, 1, 1] ∧ LexLE [2, 1, 1] [1, 1, 2])) h)
              · exact by
                  constructor
                  · exact by
                      intro _
                      exact k16t8_cover1263
                  · intro q
                    exact Fin.elim0 q
        · exact by
            constructor
            · exact by
                intro _
                exact k16t8_cover1264
            · intro q
              fin_cases q
              · exact by
                  constructor
                  · exact by
                      intro h
                      exact False.elim ((by decide : ¬ (LexLE [1, 2, 1] [3, 1] ∧ LexLE [3, 1] [1, 3])) h)
                  · intro q
                    exact Fin.elim0 q
        · exact by
            constructor
            · exact by
                intro _
                exact k16t8_cover1265
            · intro q
              exact Fin.elim0 q

private theorem k16t8_cover1266 : ∀ P ∈ pathPatterns 1 0 [1, 2, 1, 1, 1, 2], HasCheckedCertificate 16 8 ([[1, 2, 1, 1, 1, 2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [1, 2, 1, 1, 1, 2] [] ∧ LexLE [] [])) h)

private theorem k16t8_cover1267 : ∀ P ∈ pathPatterns 2 1 [1, 2, 1, 1, 2], HasCheckedCertificate 16 8 ([[1, 2, 1, 1, 2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [1, 2, 1, 1, 2] [] ∧ LexLE [] [])) h)
      · intro q
        fin_cases q
        · exact by
            intro h
            exact False.elim ((by decide : ¬ (LexLE [1, 2, 1, 1, 2] [1] ∧ LexLE [1] [1])) h)

private theorem k16t8_cover1268 : ∀ P ∈ pathPatterns 1 0 [1, 2, 1, 1, 2, 1], HasCheckedCertificate 16 8 ([[1, 2, 1, 1, 2, 1]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [1, 2, 1, 1, 2, 1] [] ∧ LexLE [] [])) h)

private theorem k16t8_cover1269 : ∀ P ∈ pathPatterns 2 0 [1, 2, 1, 1, 3], HasCheckedCertificate 16 8 ([[1, 2, 1, 1, 3]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [1, 2, 1, 1, 3] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k16t8_cover1271 : ∀ P ∈ pathPatterns 1 0 [2], HasCheckedCertificate 16 8 ([[1, 2, 1, 2], [2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [2] [] ∧ LexLE [] [])) h)

private theorem k16t8_cover1270 : ∀ P ∈ pathPatterns 3 2 [1, 2, 1, 2], HasCheckedCertificate 16 8 ([[1, 2, 1, 2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [1, 2, 1, 2] [] ∧ LexLE [] [])) h)
      · intro q
        fin_cases q
        · exact by
            constructor
            · exact by
                intro h
                exact False.elim ((by decide : ¬ (LexLE [1, 2, 1, 2] [1] ∧ LexLE [1] [1])) h)
            · intro q
              fin_cases q
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [1, 2, 1, 2] [1, 1] ∧ LexLE [1, 1] [1, 1])) h)
        · exact by
            constructor
            · exact by
                intro _
                exact k16t8_cover1271
            · intro q
              exact Fin.elim0 q

private theorem k16t8_cover1272 : ∀ P ∈ pathPatterns 2 1 [1, 2, 1, 2, 1], HasCheckedCertificate 16 8 ([[1, 2, 1, 2, 1]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [1, 2, 1, 2, 1] [] ∧ LexLE [] [])) h)
      · intro q
        fin_cases q
        · exact by
            intro h
            exact False.elim ((by decide : ¬ (LexLE [1, 2, 1, 2, 1] [1] ∧ LexLE [1] [1])) h)

private theorem k16t8_cover1273 : ∀ P ∈ pathPatterns 2 0 [1, 2, 1, 2, 2], HasCheckedCertificate 16 8 ([[1, 2, 1, 2, 2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [1, 2, 1, 2, 2] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k16t8_cover1274 : ∀ P ∈ pathPatterns 3 1 [1, 2, 1, 3], HasCheckedCertificate 16 8 ([[1, 2, 1, 3]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [1, 2, 1, 3] [] ∧ LexLE [] [])) h)
      · intro q
        fin_cases q
        · exact by
            constructor
            · exact by
                intro h
                exact False.elim ((by decide : ¬ (LexLE [1, 2, 1, 3] [1] ∧ LexLE [1] [1])) h)
            · intro q
              exact Fin.elim0 q

private theorem k16t8_cover1275 : ∀ P ∈ pathPatterns 2 0 [1, 2, 1, 3, 1], HasCheckedCertificate 16 8 ([[1, 2, 1, 3, 1]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [1, 2, 1, 3, 1] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k16t8_cover1276 : ∀ P ∈ pathPatterns 3 0 [1, 2, 1, 4], HasCheckedCertificate 16 8 ([[1, 2, 1, 4]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [1, 2, 1, 4] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k16t8_cover1278 : ∀ P ∈ pathPatterns 2 1 [2], HasCheckedCertificate 16 8 ([[1, 2, 2], [2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [2] [] ∧ LexLE [] [])) h)
      · intro q
        fin_cases q
        · exact by
            intro h
            exact False.elim ((by decide : ¬ (LexLE [2] [1] ∧ LexLE [1] [1])) h)

private theorem k16t8_cover1279 : ∀ P ∈ pathPatterns 2 0 [3], HasCheckedCertificate 16 8 ([[1, 2, 2], [3]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [3] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k16t8_cover1277 : ∀ P ∈ pathPatterns 4 3 [1, 2, 2], HasCheckedCertificate 16 8 ([[1, 2, 2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [1, 2, 2] [] ∧ LexLE [] [])) h)
      · intro q
        fin_cases q
        · exact by
            constructor
            · exact by
                intro h
                exact False.elim ((by decide : ¬ (LexLE [1, 2, 2] [1] ∧ LexLE [1] [1])) h)
            · intro q
              fin_cases q
              · exact by
                  constructor
                  · exact by
                      intro h
                      exact False.elim ((by decide : ¬ (LexLE [1, 2, 2] [1, 1] ∧ LexLE [1, 1] [1, 1])) h)
                  · intro q
                    fin_cases q
                    · exact by
                        intro h
                        exact False.elim ((by decide : ¬ (LexLE [1, 2, 2] [1, 1, 1] ∧ LexLE [1, 1, 1] [1, 1, 1])) h)
              · exact by
                  constructor
                  · exact by
                      intro h
                      exact False.elim ((by decide : ¬ (LexLE [1, 2, 2] [1, 2] ∧ LexLE [1, 2] [2, 1])) h)
                  · intro q
                    exact Fin.elim0 q
        · exact by
            constructor
            · exact by
                intro _
                exact k16t8_cover1278
            · intro q
              fin_cases q
              · exact by
                  constructor
                  · exact by
                      intro h
                      exact False.elim ((by decide : ¬ (LexLE [1, 2, 2] [2, 1] ∧ LexLE [2, 1] [1, 2])) h)
                  · intro q
                    exact Fin.elim0 q
        · exact by
            constructor
            · exact by
                intro _
                exact k16t8_cover1279
            · intro q
              exact Fin.elim0 q

private theorem k16t8_cover1281 : ∀ P ∈ pathPatterns 1 0 [2], HasCheckedCertificate 16 8 ([[1, 2, 2, 1], [2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [2] [] ∧ LexLE [] [])) h)

private theorem k16t8_cover1280 : ∀ P ∈ pathPatterns 3 2 [1, 2, 2, 1], HasCheckedCertificate 16 8 ([[1, 2, 2, 1]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [1, 2, 2, 1] [] ∧ LexLE [] [])) h)
      · intro q
        fin_cases q
        · exact by
            constructor
            · exact by
                intro h
                exact False.elim ((by decide : ¬ (LexLE [1, 2, 2, 1] [1] ∧ LexLE [1] [1])) h)
            · intro q
              fin_cases q
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [1, 2, 2, 1] [1, 1] ∧ LexLE [1, 1] [1, 1])) h)
        · exact by
            constructor
            · exact by
                intro _
                exact k16t8_cover1281
            · intro q
              exact Fin.elim0 q

private theorem k16t8_cover1282 : ∀ P ∈ pathPatterns 2 0 [1, 2, 2, 1, 2], HasCheckedCertificate 16 8 ([[1, 2, 2, 1, 2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [1, 2, 2, 1, 2] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k16t8_cover1283 : ∀ P ∈ pathPatterns 3 1 [1, 2, 2, 2], HasCheckedCertificate 16 8 ([[1, 2, 2, 2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [1, 2, 2, 2] [] ∧ LexLE [] [])) h)
      · intro q
        fin_cases q
        · exact by
            constructor
            · exact by
                intro h
                exact False.elim ((by decide : ¬ (LexLE [1, 2, 2, 2] [1] ∧ LexLE [1] [1])) h)
            · intro q
              exact Fin.elim0 q

private theorem k16t8_cover1284 : ∀ P ∈ pathPatterns 2 0 [1, 2, 2, 2, 1], HasCheckedCertificate 16 8 ([[1, 2, 2, 2, 1]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [1, 2, 2, 2, 1] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k16t8_cover1285 : ∀ P ∈ pathPatterns 3 0 [1, 2, 2, 3], HasCheckedCertificate 16 8 ([[1, 2, 2, 3]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [1, 2, 2, 3] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k16t8_cover1287 : ∀ P ∈ pathPatterns 2 0 [2], HasCheckedCertificate 16 8 ([[1, 2, 3], [2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [2] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k16t8_cover1286 : ∀ P ∈ pathPatterns 4 2 [1, 2, 3], HasCheckedCertificate 16 8 ([[1, 2, 3]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [1, 2, 3] [] ∧ LexLE [] [])) h)
      · intro q
        fin_cases q
        · exact by
            constructor
            · exact by
                intro h
                exact False.elim ((by decide : ¬ (LexLE [1, 2, 3] [1] ∧ LexLE [1] [1])) h)
            · intro q
              fin_cases q
              · exact by
                  constructor
                  · exact by
                      intro h
                      exact False.elim ((by decide : ¬ (LexLE [1, 2, 3] [1, 1] ∧ LexLE [1, 1] [1, 1])) h)
                  · intro q
                    exact Fin.elim0 q
        · exact by
            constructor
            · exact by
                intro _
                exact k16t8_cover1287
            · intro q
              exact Fin.elim0 q

private theorem k16t8_cover1288 : ∀ P ∈ pathPatterns 3 1 [1, 2, 3, 1], HasCheckedCertificate 16 8 ([[1, 2, 3, 1]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [1, 2, 3, 1] [] ∧ LexLE [] [])) h)
      · intro q
        fin_cases q
        · exact by
            constructor
            · exact by
                intro h
                exact False.elim ((by decide : ¬ (LexLE [1, 2, 3, 1] [1] ∧ LexLE [1] [1])) h)
            · intro q
              exact Fin.elim0 q

private theorem k16t8_cover1289 : ∀ P ∈ pathPatterns 3 0 [1, 2, 3, 2], HasCheckedCertificate 16 8 ([[1, 2, 3, 2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [1, 2, 3, 2] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k16t8_cover1290 : ∀ P ∈ pathPatterns 4 1 [1, 2, 4], HasCheckedCertificate 16 8 ([[1, 2, 4]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [1, 2, 4] [] ∧ LexLE [] [])) h)
      · intro q
        fin_cases q
        · exact by
            constructor
            · exact by
                intro h
                exact False.elim ((by decide : ¬ (LexLE [1, 2, 4] [1] ∧ LexLE [1] [1])) h)
            · intro q
              exact Fin.elim0 q

private theorem k16t8_cover1291 : ∀ P ∈ pathPatterns 3 0 [1, 2, 4, 1], HasCheckedCertificate 16 8 ([[1, 2, 4, 1]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [1, 2, 4, 1] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k16t8_cover1292 : ∀ P ∈ pathPatterns 4 0 [1, 2, 5], HasCheckedCertificate 16 8 ([[1, 2, 5]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [1, 2, 5] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k16t8_seq1239 : amountSequenceForall 5 5 (fun tail =>
    (LexLE [] ([1, 2] ++ tail) ∧ LexLE ([1, 2] ++ tail) ([1, 2] ++ tail).reverse) →
    ∀ P ∈ pathPatterns (7 - ([1, 2] ++ tail).length) (8 - ([1, 2] ++ tail).sum) ([1, 2] ++ tail),
      HasCheckedCertificate 16 8 ([] ++ (([1, 2] ++ tail) :: P))) :=
by
  constructor
  · exact by
      intro _
      exact k16t8_cover1240
  · intro q
    fin_cases q
    · exact by
        constructor
        · exact by
            intro _
            exact k16t8_cover1258
        · intro q
          fin_cases q
          · exact by
              constructor
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [] [1, 2, 1, 1] ∧ LexLE [1, 2, 1, 1] [1, 1, 2, 1])) h)
              · intro q
                fin_cases q
                · exact by
                    constructor
                    · exact by
                        intro h
                        exact False.elim ((by decide : ¬ (LexLE [] [1, 2, 1, 1, 1] ∧ LexLE [1, 2, 1, 1, 1] [1, 1, 1, 2, 1])) h)
                    · intro q
                      fin_cases q
                      · exact by
                          constructor
                          · exact by
                              intro h
                              exact False.elim ((by decide : ¬ (LexLE [] [1, 2, 1, 1, 1, 1] ∧ LexLE [1, 2, 1, 1, 1, 1] [1, 1, 1, 1, 2, 1])) h)
                          · intro q
                            fin_cases q
                            · exact by
                                intro h
                                exact False.elim ((by decide : ¬ (LexLE [] [1, 2, 1, 1, 1, 1, 1] ∧ LexLE [1, 2, 1, 1, 1, 1, 1] [1, 1, 1, 1, 1, 2, 1])) h)
                      · exact by
                          constructor
                          · exact by
                              intro _
                              exact k16t8_cover1266
                          · intro q
                            exact Fin.elim0 q
                · exact by
                    constructor
                    · exact by
                        intro _
                        exact k16t8_cover1267
                    · intro q
                      fin_cases q
                      · exact by
                          constructor
                          · exact by
                              intro _
                              exact k16t8_cover1268
                          · intro q
                            exact Fin.elim0 q
                · exact by
                    constructor
                    · exact by
                        intro _
                        exact k16t8_cover1269
                    · intro q
                      exact Fin.elim0 q
          · exact by
              constructor
              · exact by
                  intro _
                  exact k16t8_cover1270
              · intro q
                fin_cases q
                · exact by
                    constructor
                    · exact by
                        intro _
                        exact k16t8_cover1272
                    · intro q
                      fin_cases q
                      · exact by
                          constructor
                          · exact by
                              intro h
                              exact False.elim ((by decide : ¬ (LexLE [] [1, 2, 1, 2, 1, 1] ∧ LexLE [1, 2, 1, 2, 1, 1] [1, 1, 2, 1, 2, 1])) h)
                          · intro q
                            exact Fin.elim0 q
                · exact by
                    constructor
                    · exact by
                        intro _
                        exact k16t8_cover1273
                    · intro q
                      exact Fin.elim0 q
          · exact by
              constructor
              · exact by
                  intro _
                  exact k16t8_cover1274
              · intro q
                fin_cases q
                · exact by
                    constructor
                    · exact by
                        intro _
                        exact k16t8_cover1275
                    · intro q
                      exact Fin.elim0 q
          · exact by
              constructor
              · exact by
                  intro _
                  exact k16t8_cover1276
              · intro q
                exact Fin.elim0 q
    · exact by
        constructor
        · exact by
            intro _
            exact k16t8_cover1277
        · intro q
          fin_cases q
          · exact by
              constructor
              · exact by
                  intro _
                  exact k16t8_cover1280
              · intro q
                fin_cases q
                · exact by
                    constructor
                    · exact by
                        intro h
                        exact False.elim ((by decide : ¬ (LexLE [] [1, 2, 2, 1, 1] ∧ LexLE [1, 2, 2, 1, 1] [1, 1, 2, 2, 1])) h)
                    · intro q
                      fin_cases q
                      · exact by
                          constructor
                          · exact by
                              intro h
                              exact False.elim ((by decide : ¬ (LexLE [] [1, 2, 2, 1, 1, 1] ∧ LexLE [1, 2, 2, 1, 1, 1] [1, 1, 1, 2, 2, 1])) h)
                          · intro q
                            exact Fin.elim0 q
                · exact by
                    constructor
                    · exact by
                        intro _
                        exact k16t8_cover1282
                    · intro q
                      exact Fin.elim0 q
          · exact by
              constructor
              · exact by
                  intro _
                  exact k16t8_cover1283
              · intro q
                fin_cases q
                · exact by
                    constructor
                    · exact by
                        intro _
                        exact k16t8_cover1284
                    · intro q
                      exact Fin.elim0 q
          · exact by
              constructor
              · exact by
                  intro _
                  exact k16t8_cover1285
              · intro q
                exact Fin.elim0 q
    · exact by
        constructor
        · exact by
            intro _
            exact k16t8_cover1286
        · intro q
          fin_cases q
          · exact by
              constructor
              · exact by
                  intro _
                  exact k16t8_cover1288
              · intro q
                fin_cases q
                · exact by
                    constructor
                    · exact by
                        intro h
                        exact False.elim ((by decide : ¬ (LexLE [] [1, 2, 3, 1, 1] ∧ LexLE [1, 2, 3, 1, 1] [1, 1, 3, 2, 1])) h)
                    · intro q
                      exact Fin.elim0 q
          · exact by
              constructor
              · exact by
                  intro _
                  exact k16t8_cover1289
              · intro q
                exact Fin.elim0 q
    · exact by
        constructor
        · exact by
            intro _
            exact k16t8_cover1290
        · intro q
          fin_cases q
          · exact by
              constructor
              · exact by
                  intro _
                  exact k16t8_cover1291
              · intro q
                exact Fin.elim0 q
    · exact by
        constructor
        · exact by
            intro _
            exact k16t8_cover1292
        · intro q
          exact Fin.elim0 q

private theorem k16t8_cover1294 : ∀ P ∈ pathPatterns 2 0 [1, 3], HasCheckedCertificate 16 8 ([[1, 3], [1, 3]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [1, 3] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k16t8_cover1296 : ∀ P ∈ pathPatterns 1 0 [2], HasCheckedCertificate 16 8 ([[1, 3], [2], [2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [2] [] ∧ LexLE [] [])) h)

private theorem k16t8_cover1295 : ∀ P ∈ pathPatterns 3 2 [2], HasCheckedCertificate 16 8 ([[1, 3], [2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [2] [] ∧ LexLE [] [])) h)
      · intro q
        fin_cases q
        · exact by
            constructor
            · exact by
                intro h
                exact False.elim ((by decide : ¬ (LexLE [2] [1] ∧ LexLE [1] [1])) h)
            · intro q
              fin_cases q
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [2] [1, 1] ∧ LexLE [1, 1] [1, 1])) h)
        · exact by
            constructor
            · exact by
                intro _
                exact k16t8_cover1296
            · intro q
              exact Fin.elim0 q

private theorem k16t8_cover1297 : ∀ P ∈ pathPatterns 2 0 [2, 2], HasCheckedCertificate 16 8 ([[1, 3], [2, 2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [2, 2] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k16t8_cover1298 : ∀ P ∈ pathPatterns 3 1 [3], HasCheckedCertificate 16 8 ([[1, 3], [3]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [3] [] ∧ LexLE [] [])) h)
      · intro q
        fin_cases q
        · exact by
            constructor
            · exact by
                intro h
                exact False.elim ((by decide : ¬ (LexLE [3] [1] ∧ LexLE [1] [1])) h)
            · intro q
              exact Fin.elim0 q

private theorem k16t8_cover1299 : ∀ P ∈ pathPatterns 3 0 [4], HasCheckedCertificate 16 8 ([[1, 3], [4]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [4] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k16t8_cover1293 : ∀ P ∈ pathPatterns 5 4 [1, 3], HasCheckedCertificate 16 8 ([[1, 3]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [1, 3] [] ∧ LexLE [] [])) h)
      · intro q
        fin_cases q
        · exact by
            constructor
            · exact by
                intro h
                exact False.elim ((by decide : ¬ (LexLE [1, 3] [1] ∧ LexLE [1] [1])) h)
            · intro q
              fin_cases q
              · exact by
                  constructor
                  · exact by
                      intro h
                      exact False.elim ((by decide : ¬ (LexLE [1, 3] [1, 1] ∧ LexLE [1, 1] [1, 1])) h)
                  · intro q
                    fin_cases q
                    · exact by
                        constructor
                        · exact by
                            intro h
                            exact False.elim ((by decide : ¬ (LexLE [1, 3] [1, 1, 1] ∧ LexLE [1, 1, 1] [1, 1, 1])) h)
                        · intro q
                          fin_cases q
                          · exact by
                              intro h
                              exact False.elim ((by decide : ¬ (LexLE [1, 3] [1, 1, 1, 1] ∧ LexLE [1, 1, 1, 1] [1, 1, 1, 1])) h)
                    · exact by
                        constructor
                        · exact by
                            intro h
                            exact False.elim ((by decide : ¬ (LexLE [1, 3] [1, 1, 2] ∧ LexLE [1, 1, 2] [2, 1, 1])) h)
                        · intro q
                          exact Fin.elim0 q
              · exact by
                  constructor
                  · exact by
                      intro h
                      exact False.elim ((by decide : ¬ (LexLE [1, 3] [1, 2] ∧ LexLE [1, 2] [2, 1])) h)
                  · intro q
                    fin_cases q
                    · exact by
                        constructor
                        · exact by
                            intro h
                            exact False.elim ((by decide : ¬ (LexLE [1, 3] [1, 2, 1] ∧ LexLE [1, 2, 1] [1, 2, 1])) h)
                        · intro q
                          exact Fin.elim0 q
              · exact by
                  constructor
                  · exact by
                      intro _
                      exact k16t8_cover1294
                  · intro q
                    exact Fin.elim0 q
        · exact by
            constructor
            · exact by
                intro _
                exact k16t8_cover1295
            · intro q
              fin_cases q
              · exact by
                  constructor
                  · exact by
                      intro h
                      exact False.elim ((by decide : ¬ (LexLE [1, 3] [2, 1] ∧ LexLE [2, 1] [1, 2])) h)
                  · intro q
                    fin_cases q
                    · exact by
                        constructor
                        · exact by
                            intro h
                            exact False.elim ((by decide : ¬ (LexLE [1, 3] [2, 1, 1] ∧ LexLE [2, 1, 1] [1, 1, 2])) h)
                        · intro q
                          exact Fin.elim0 q
              · exact by
                  constructor
                  · exact by
                      intro _
                      exact k16t8_cover1297
                  · intro q
                    exact Fin.elim0 q
        · exact by
            constructor
            · exact by
                intro _
                exact k16t8_cover1298
            · intro q
              fin_cases q
              · exact by
                  constructor
                  · exact by
                      intro h
                      exact False.elim ((by decide : ¬ (LexLE [1, 3] [3, 1] ∧ LexLE [3, 1] [1, 3])) h)
                  · intro q
                    exact Fin.elim0 q
        · exact by
            constructor
            · exact by
                intro _
                exact k16t8_cover1299
            · intro q
              exact Fin.elim0 q

private theorem k16t8_cover1301 : ∀ P ∈ pathPatterns 2 1 [2], HasCheckedCertificate 16 8 ([[1, 3, 1], [2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [2] [] ∧ LexLE [] [])) h)
      · intro q
        fin_cases q
        · exact by
            intro h
            exact False.elim ((by decide : ¬ (LexLE [2] [1] ∧ LexLE [1] [1])) h)

private theorem k16t8_cover1302 : ∀ P ∈ pathPatterns 2 0 [3], HasCheckedCertificate 16 8 ([[1, 3, 1], [3]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [3] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k16t8_cover1300 : ∀ P ∈ pathPatterns 4 3 [1, 3, 1], HasCheckedCertificate 16 8 ([[1, 3, 1]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [1, 3, 1] [] ∧ LexLE [] [])) h)
      · intro q
        fin_cases q
        · exact by
            constructor
            · exact by
                intro h
                exact False.elim ((by decide : ¬ (LexLE [1, 3, 1] [1] ∧ LexLE [1] [1])) h)
            · intro q
              fin_cases q
              · exact by
                  constructor
                  · exact by
                      intro h
                      exact False.elim ((by decide : ¬ (LexLE [1, 3, 1] [1, 1] ∧ LexLE [1, 1] [1, 1])) h)
                  · intro q
                    fin_cases q
                    · exact by
                        intro h
                        exact False.elim ((by decide : ¬ (LexLE [1, 3, 1] [1, 1, 1] ∧ LexLE [1, 1, 1] [1, 1, 1])) h)
              · exact by
                  constructor
                  · exact by
                      intro h
                      exact False.elim ((by decide : ¬ (LexLE [1, 3, 1] [1, 2] ∧ LexLE [1, 2] [2, 1])) h)
                  · intro q
                    exact Fin.elim0 q
        · exact by
            constructor
            · exact by
                intro _
                exact k16t8_cover1301
            · intro q
              fin_cases q
              · exact by
                  constructor
                  · exact by
                      intro h
                      exact False.elim ((by decide : ¬ (LexLE [1, 3, 1] [2, 1] ∧ LexLE [2, 1] [1, 2])) h)
                  · intro q
                    exact Fin.elim0 q
        · exact by
            constructor
            · exact by
                intro _
                exact k16t8_cover1302
            · intro q
              exact Fin.elim0 q

private theorem k16t8_cover1303 : ∀ P ∈ pathPatterns 2 0 [1, 3, 1, 1, 2], HasCheckedCertificate 16 8 ([[1, 3, 1, 1, 2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [1, 3, 1, 1, 2] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k16t8_cover1304 : ∀ P ∈ pathPatterns 3 1 [1, 3, 1, 2], HasCheckedCertificate 16 8 ([[1, 3, 1, 2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [1, 3, 1, 2] [] ∧ LexLE [] [])) h)
      · intro q
        fin_cases q
        · exact by
            constructor
            · exact by
                intro h
                exact False.elim ((by decide : ¬ (LexLE [1, 3, 1, 2] [1] ∧ LexLE [1] [1])) h)
            · intro q
              exact Fin.elim0 q

private theorem k16t8_cover1305 : ∀ P ∈ pathPatterns 3 0 [1, 3, 1, 3], HasCheckedCertificate 16 8 ([[1, 3, 1, 3]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [1, 3, 1, 3] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k16t8_cover1307 : ∀ P ∈ pathPatterns 2 0 [2], HasCheckedCertificate 16 8 ([[1, 3, 2], [2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [2] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k16t8_cover1306 : ∀ P ∈ pathPatterns 4 2 [1, 3, 2], HasCheckedCertificate 16 8 ([[1, 3, 2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [1, 3, 2] [] ∧ LexLE [] [])) h)
      · intro q
        fin_cases q
        · exact by
            constructor
            · exact by
                intro h
                exact False.elim ((by decide : ¬ (LexLE [1, 3, 2] [1] ∧ LexLE [1] [1])) h)
            · intro q
              fin_cases q
              · exact by
                  constructor
                  · exact by
                      intro h
                      exact False.elim ((by decide : ¬ (LexLE [1, 3, 2] [1, 1] ∧ LexLE [1, 1] [1, 1])) h)
                  · intro q
                    exact Fin.elim0 q
        · exact by
            constructor
            · exact by
                intro _
                exact k16t8_cover1307
            · intro q
              exact Fin.elim0 q

private theorem k16t8_cover1308 : ∀ P ∈ pathPatterns 3 0 [1, 3, 2, 2], HasCheckedCertificate 16 8 ([[1, 3, 2, 2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [1, 3, 2, 2] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k16t8_cover1309 : ∀ P ∈ pathPatterns 4 1 [1, 3, 3], HasCheckedCertificate 16 8 ([[1, 3, 3]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [1, 3, 3] [] ∧ LexLE [] [])) h)
      · intro q
        fin_cases q
        · exact by
            constructor
            · exact by
                intro h
                exact False.elim ((by decide : ¬ (LexLE [1, 3, 3] [1] ∧ LexLE [1] [1])) h)
            · intro q
              exact Fin.elim0 q

private theorem k16t8_cover1310 : ∀ P ∈ pathPatterns 3 0 [1, 3, 3, 1], HasCheckedCertificate 16 8 ([[1, 3, 3, 1]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [1, 3, 3, 1] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k16t8_cover1311 : ∀ P ∈ pathPatterns 4 0 [1, 3, 4], HasCheckedCertificate 16 8 ([[1, 3, 4]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [1, 3, 4] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k16t8_cover1313 : ∀ P ∈ pathPatterns 3 1 [2], HasCheckedCertificate 16 8 ([[1, 4], [2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [2] [] ∧ LexLE [] [])) h)
      · intro q
        fin_cases q
        · exact by
            constructor
            · exact by
                intro h
                exact False.elim ((by decide : ¬ (LexLE [2] [1] ∧ LexLE [1] [1])) h)
            · intro q
              exact Fin.elim0 q

private theorem k16t8_cover1314 : ∀ P ∈ pathPatterns 3 0 [3], HasCheckedCertificate 16 8 ([[1, 4], [3]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [3] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k16t8_cover1312 : ∀ P ∈ pathPatterns 5 3 [1, 4], HasCheckedCertificate 16 8 ([[1, 4]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [1, 4] [] ∧ LexLE [] [])) h)
      · intro q
        fin_cases q
        · exact by
            constructor
            · exact by
                intro h
                exact False.elim ((by decide : ¬ (LexLE [1, 4] [1] ∧ LexLE [1] [1])) h)
            · intro q
              fin_cases q
              · exact by
                  constructor
                  · exact by
                      intro h
                      exact False.elim ((by decide : ¬ (LexLE [1, 4] [1, 1] ∧ LexLE [1, 1] [1, 1])) h)
                  · intro q
                    fin_cases q
                    · exact by
                        constructor
                        · exact by
                            intro h
                            exact False.elim ((by decide : ¬ (LexLE [1, 4] [1, 1, 1] ∧ LexLE [1, 1, 1] [1, 1, 1])) h)
                        · intro q
                          exact Fin.elim0 q
              · exact by
                  constructor
                  · exact by
                      intro h
                      exact False.elim ((by decide : ¬ (LexLE [1, 4] [1, 2] ∧ LexLE [1, 2] [2, 1])) h)
                  · intro q
                    exact Fin.elim0 q
        · exact by
            constructor
            · exact by
                intro _
                exact k16t8_cover1313
            · intro q
              fin_cases q
              · exact by
                  constructor
                  · exact by
                      intro h
                      exact False.elim ((by decide : ¬ (LexLE [1, 4] [2, 1] ∧ LexLE [2, 1] [1, 2])) h)
                  · intro q
                    exact Fin.elim0 q
        · exact by
            constructor
            · exact by
                intro _
                exact k16t8_cover1314
            · intro q
              exact Fin.elim0 q

private theorem k16t8_cover1316 : ∀ P ∈ pathPatterns 2 0 [2], HasCheckedCertificate 16 8 ([[1, 4, 1], [2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [2] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k16t8_cover1315 : ∀ P ∈ pathPatterns 4 2 [1, 4, 1], HasCheckedCertificate 16 8 ([[1, 4, 1]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [1, 4, 1] [] ∧ LexLE [] [])) h)
      · intro q
        fin_cases q
        · exact by
            constructor
            · exact by
                intro h
                exact False.elim ((by decide : ¬ (LexLE [1, 4, 1] [1] ∧ LexLE [1] [1])) h)
            · intro q
              fin_cases q
              · exact by
                  constructor
                  · exact by
                      intro h
                      exact False.elim ((by decide : ¬ (LexLE [1, 4, 1] [1, 1] ∧ LexLE [1, 1] [1, 1])) h)
                  · intro q
                    exact Fin.elim0 q
        · exact by
            constructor
            · exact by
                intro _
                exact k16t8_cover1316
            · intro q
              exact Fin.elim0 q

private theorem k16t8_cover1317 : ∀ P ∈ pathPatterns 3 0 [1, 4, 1, 2], HasCheckedCertificate 16 8 ([[1, 4, 1, 2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [1, 4, 1, 2] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k16t8_cover1318 : ∀ P ∈ pathPatterns 4 1 [1, 4, 2], HasCheckedCertificate 16 8 ([[1, 4, 2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [1, 4, 2] [] ∧ LexLE [] [])) h)
      · intro q
        fin_cases q
        · exact by
            constructor
            · exact by
                intro h
                exact False.elim ((by decide : ¬ (LexLE [1, 4, 2] [1] ∧ LexLE [1] [1])) h)
            · intro q
              exact Fin.elim0 q

private theorem k16t8_cover1319 : ∀ P ∈ pathPatterns 4 0 [1, 4, 3], HasCheckedCertificate 16 8 ([[1, 4, 3]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [1, 4, 3] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k16t8_cover1321 : ∀ P ∈ pathPatterns 3 0 [2], HasCheckedCertificate 16 8 ([[1, 5], [2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [2] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k16t8_cover1320 : ∀ P ∈ pathPatterns 5 2 [1, 5], HasCheckedCertificate 16 8 ([[1, 5]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [1, 5] [] ∧ LexLE [] [])) h)
      · intro q
        fin_cases q
        · exact by
            constructor
            · exact by
                intro h
                exact False.elim ((by decide : ¬ (LexLE [1, 5] [1] ∧ LexLE [1] [1])) h)
            · intro q
              fin_cases q
              · exact by
                  constructor
                  · exact by
                      intro h
                      exact False.elim ((by decide : ¬ (LexLE [1, 5] [1, 1] ∧ LexLE [1, 1] [1, 1])) h)
                  · intro q
                    exact Fin.elim0 q
        · exact by
            constructor
            · exact by
                intro _
                exact k16t8_cover1321
            · intro q
              exact Fin.elim0 q

private theorem k16t8_cover1322 : ∀ P ∈ pathPatterns 4 1 [1, 5, 1], HasCheckedCertificate 16 8 ([[1, 5, 1]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [1, 5, 1] [] ∧ LexLE [] [])) h)
      · intro q
        fin_cases q
        · exact by
            constructor
            · exact by
                intro h
                exact False.elim ((by decide : ¬ (LexLE [1, 5, 1] [1] ∧ LexLE [1] [1])) h)
            · intro q
              exact Fin.elim0 q

private theorem k16t8_cover1323 : ∀ P ∈ pathPatterns 4 0 [1, 5, 2], HasCheckedCertificate 16 8 ([[1, 5, 2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [1, 5, 2] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k16t8_cover1324 : ∀ P ∈ pathPatterns 5 1 [1, 6], HasCheckedCertificate 16 8 ([[1, 6]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [1, 6] [] ∧ LexLE [] [])) h)
      · intro q
        fin_cases q
        · exact by
            constructor
            · exact by
                intro h
                exact False.elim ((by decide : ¬ (LexLE [1, 6] [1] ∧ LexLE [1] [1])) h)
            · intro q
              exact Fin.elim0 q

private theorem k16t8_cover1325 : ∀ P ∈ pathPatterns 4 0 [1, 6, 1], HasCheckedCertificate 16 8 ([[1, 6, 1]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [1, 6, 1] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k16t8_cover1326 : ∀ P ∈ pathPatterns 5 0 [1, 7], HasCheckedCertificate 16 8 ([[1, 7]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [1, 7] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k16t8_seq917 : amountSequenceForall 6 7 (fun tail =>
    (LexLE [] ([1] ++ tail) ∧ LexLE ([1] ++ tail) ([1] ++ tail).reverse) →
    ∀ P ∈ pathPatterns (7 - ([1] ++ tail).length) (8 - ([1] ++ tail).sum) ([1] ++ tail),
      HasCheckedCertificate 16 8 ([] ++ (([1] ++ tail) :: P))) :=
by
  constructor
  · exact by
      intro _
      exact k16t8_cover918
  · intro q
    fin_cases q
    · exact k16t8_seq1076

    · exact k16t8_seq1239

    · exact by
        constructor
        · exact by
            intro _
            exact k16t8_cover1293
        · intro q
          fin_cases q
          · exact by
              constructor
              · exact by
                  intro _
                  exact k16t8_cover1300
              · intro q
                fin_cases q
                · exact by
                    constructor
                    · exact by
                        intro h
                        exact False.elim ((by decide : ¬ (LexLE [] [1, 3, 1, 1] ∧ LexLE [1, 3, 1, 1] [1, 1, 3, 1])) h)
                    · intro q
                      fin_cases q
                      · exact by
                          constructor
                          · exact by
                              intro h
                              exact False.elim ((by decide : ¬ (LexLE [] [1, 3, 1, 1, 1] ∧ LexLE [1, 3, 1, 1, 1] [1, 1, 1, 3, 1])) h)
                          · intro q
                            fin_cases q
                            · exact by
                                constructor
                                · exact by
                                    intro h
                                    exact False.elim ((by decide : ¬ (LexLE [] [1, 3, 1, 1, 1, 1] ∧ LexLE [1, 3, 1, 1, 1, 1] [1, 1, 1, 1, 3, 1])) h)
                                · intro q
                                  exact Fin.elim0 q
                      · exact by
                          constructor
                          · exact by
                              intro _
                              exact k16t8_cover1303
                          · intro q
                            exact Fin.elim0 q
                · exact by
                    constructor
                    · exact by
                        intro _
                        exact k16t8_cover1304
                    · intro q
                      fin_cases q
                      · exact by
                          constructor
                          · exact by
                              intro h
                              exact False.elim ((by decide : ¬ (LexLE [] [1, 3, 1, 2, 1] ∧ LexLE [1, 3, 1, 2, 1] [1, 2, 1, 3, 1])) h)
                          · intro q
                            exact Fin.elim0 q
                · exact by
                    constructor
                    · exact by
                        intro _
                        exact k16t8_cover1305
                    · intro q
                      exact Fin.elim0 q
          · exact by
              constructor
              · exact by
                  intro _
                  exact k16t8_cover1306
              · intro q
                fin_cases q
                · exact by
                    constructor
                    · exact by
                        intro h
                        exact False.elim ((by decide : ¬ (LexLE [] [1, 3, 2, 1] ∧ LexLE [1, 3, 2, 1] [1, 2, 3, 1])) h)
                    · intro q
                      fin_cases q
                      · exact by
                          constructor
                          · exact by
                              intro h
                              exact False.elim ((by decide : ¬ (LexLE [] [1, 3, 2, 1, 1] ∧ LexLE [1, 3, 2, 1, 1] [1, 1, 2, 3, 1])) h)
                          · intro q
                            exact Fin.elim0 q
                · exact by
                    constructor
                    · exact by
                        intro _
                        exact k16t8_cover1308
                    · intro q
                      exact Fin.elim0 q
          · exact by
              constructor
              · exact by
                  intro _
                  exact k16t8_cover1309
              · intro q
                fin_cases q
                · exact by
                    constructor
                    · exact by
                        intro _
                        exact k16t8_cover1310
                    · intro q
                      exact Fin.elim0 q
          · exact by
              constructor
              · exact by
                  intro _
                  exact k16t8_cover1311
              · intro q
                exact Fin.elim0 q
    · exact by
        constructor
        · exact by
            intro _
            exact k16t8_cover1312
        · intro q
          fin_cases q
          · exact by
              constructor
              · exact by
                  intro _
                  exact k16t8_cover1315
              · intro q
                fin_cases q
                · exact by
                    constructor
                    · exact by
                        intro h
                        exact False.elim ((by decide : ¬ (LexLE [] [1, 4, 1, 1] ∧ LexLE [1, 4, 1, 1] [1, 1, 4, 1])) h)
                    · intro q
                      fin_cases q
                      · exact by
                          constructor
                          · exact by
                              intro h
                              exact False.elim ((by decide : ¬ (LexLE [] [1, 4, 1, 1, 1] ∧ LexLE [1, 4, 1, 1, 1] [1, 1, 1, 4, 1])) h)
                          · intro q
                            exact Fin.elim0 q
                · exact by
                    constructor
                    · exact by
                        intro _
                        exact k16t8_cover1317
                    · intro q
                      exact Fin.elim0 q
          · exact by
              constructor
              · exact by
                  intro _
                  exact k16t8_cover1318
              · intro q
                fin_cases q
                · exact by
                    constructor
                    · exact by
                        intro h
                        exact False.elim ((by decide : ¬ (LexLE [] [1, 4, 2, 1] ∧ LexLE [1, 4, 2, 1] [1, 2, 4, 1])) h)
                    · intro q
                      exact Fin.elim0 q
          · exact by
              constructor
              · exact by
                  intro _
                  exact k16t8_cover1319
              · intro q
                exact Fin.elim0 q
    · exact by
        constructor
        · exact by
            intro _
            exact k16t8_cover1320
        · intro q
          fin_cases q
          · exact by
              constructor
              · exact by
                  intro _
                  exact k16t8_cover1322
              · intro q
                fin_cases q
                · exact by
                    constructor
                    · exact by
                        intro h
                        exact False.elim ((by decide : ¬ (LexLE [] [1, 5, 1, 1] ∧ LexLE [1, 5, 1, 1] [1, 1, 5, 1])) h)
                    · intro q
                      exact Fin.elim0 q
          · exact by
              constructor
              · exact by
                  intro _
                  exact k16t8_cover1323
              · intro q
                exact Fin.elim0 q
    · exact by
        constructor
        · exact by
            intro _
            exact k16t8_cover1324
        · intro q
          fin_cases q
          · exact by
              constructor
              · exact by
                  intro _
                  exact k16t8_cover1325
              · intro q
                exact Fin.elim0 q
    · exact by
        constructor
        · exact by
            intro _
            exact k16t8_cover1326
        · intro q
          exact Fin.elim0 q

private theorem k16t8_seq1330 : amountSequenceForall 4 5 (fun tail =>
    (LexLE [2] ([1] ++ tail) ∧ LexLE ([1] ++ tail) ([1] ++ tail).reverse) →
    ∀ P ∈ pathPatterns (5 - ([1] ++ tail).length) (6 - ([1] ++ tail).sum) ([1] ++ tail),
      HasCheckedCertificate 16 8 ([[2]] ++ (([1] ++ tail) :: P))) :=
by
  constructor
  · exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [2] [1] ∧ LexLE [1] [1])) h)
  · intro q
    fin_cases q
    · exact by
        constructor
        · exact by
            intro h
            exact False.elim ((by decide : ¬ (LexLE [2] [1, 1] ∧ LexLE [1, 1] [1, 1])) h)
        · intro q
          fin_cases q
          · exact by
              constructor
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [2] [1, 1, 1] ∧ LexLE [1, 1, 1] [1, 1, 1])) h)
              · intro q
                fin_cases q
                · exact by
                    constructor
                    · exact by
                        intro h
                        exact False.elim ((by decide : ¬ (LexLE [2] [1, 1, 1, 1] ∧ LexLE [1, 1, 1, 1] [1, 1, 1, 1])) h)
                    · intro q
                      fin_cases q
                      · exact by
                          intro h
                          exact False.elim ((by decide : ¬ (LexLE [2] [1, 1, 1, 1, 1] ∧ LexLE [1, 1, 1, 1, 1] [1, 1, 1, 1, 1])) h)
                      · exact by
                          intro h
                          exact False.elim ((by decide : ¬ (LexLE [2] [1, 1, 1, 1, 2] ∧ LexLE [1, 1, 1, 1, 2] [2, 1, 1, 1, 1])) h)
                · exact by
                    constructor
                    · exact by
                        intro h
                        exact False.elim ((by decide : ¬ (LexLE [2] [1, 1, 1, 2] ∧ LexLE [1, 1, 1, 2] [2, 1, 1, 1])) h)
                    · intro q
                      fin_cases q
                      · exact by
                          intro h
                          exact False.elim ((by decide : ¬ (LexLE [2] [1, 1, 1, 2, 1] ∧ LexLE [1, 1, 1, 2, 1] [1, 2, 1, 1, 1])) h)
                · exact by
                    constructor
                    · exact by
                        intro h
                        exact False.elim ((by decide : ¬ (LexLE [2] [1, 1, 1, 3] ∧ LexLE [1, 1, 1, 3] [3, 1, 1, 1])) h)
                    · intro q
                      exact Fin.elim0 q
          · exact by
              constructor
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [2] [1, 1, 2] ∧ LexLE [1, 1, 2] [2, 1, 1])) h)
              · intro q
                fin_cases q
                · exact by
                    constructor
                    · exact by
                        intro h
                        exact False.elim ((by decide : ¬ (LexLE [2] [1, 1, 2, 1] ∧ LexLE [1, 1, 2, 1] [1, 2, 1, 1])) h)
                    · intro q
                      fin_cases q
                      · exact by
                          intro h
                          exact False.elim ((by decide : ¬ (LexLE [2] [1, 1, 2, 1, 1] ∧ LexLE [1, 1, 2, 1, 1] [1, 1, 2, 1, 1])) h)
                · exact by
                    constructor
                    · exact by
                        intro h
                        exact False.elim ((by decide : ¬ (LexLE [2] [1, 1, 2, 2] ∧ LexLE [1, 1, 2, 2] [2, 2, 1, 1])) h)
                    · intro q
                      exact Fin.elim0 q
          · exact by
              constructor
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [2] [1, 1, 3] ∧ LexLE [1, 1, 3] [3, 1, 1])) h)
              · intro q
                fin_cases q
                · exact by
                    constructor
                    · exact by
                        intro h
                        exact False.elim ((by decide : ¬ (LexLE [2] [1, 1, 3, 1] ∧ LexLE [1, 1, 3, 1] [1, 3, 1, 1])) h)
                    · intro q
                      exact Fin.elim0 q
          · exact by
              constructor
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [2] [1, 1, 4] ∧ LexLE [1, 1, 4] [4, 1, 1])) h)
              · intro q
                exact Fin.elim0 q
    · exact by
        constructor
        · exact by
            intro h
            exact False.elim ((by decide : ¬ (LexLE [2] [1, 2] ∧ LexLE [1, 2] [2, 1])) h)
        · intro q
          fin_cases q
          · exact by
              constructor
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [2] [1, 2, 1] ∧ LexLE [1, 2, 1] [1, 2, 1])) h)
              · intro q
                fin_cases q
                · exact by
                    constructor
                    · exact by
                        intro h
                        exact False.elim ((by decide : ¬ (LexLE [2] [1, 2, 1, 1] ∧ LexLE [1, 2, 1, 1] [1, 1, 2, 1])) h)
                    · intro q
                      fin_cases q
                      · exact by
                          intro h
                          exact False.elim ((by decide : ¬ (LexLE [2] [1, 2, 1, 1, 1] ∧ LexLE [1, 2, 1, 1, 1] [1, 1, 1, 2, 1])) h)
                · exact by
                    constructor
                    · exact by
                        intro h
                        exact False.elim ((by decide : ¬ (LexLE [2] [1, 2, 1, 2] ∧ LexLE [1, 2, 1, 2] [2, 1, 2, 1])) h)
                    · intro q
                      exact Fin.elim0 q
          · exact by
              constructor
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [2] [1, 2, 2] ∧ LexLE [1, 2, 2] [2, 2, 1])) h)
              · intro q
                fin_cases q
                · exact by
                    constructor
                    · exact by
                        intro h
                        exact False.elim ((by decide : ¬ (LexLE [2] [1, 2, 2, 1] ∧ LexLE [1, 2, 2, 1] [1, 2, 2, 1])) h)
                    · intro q
                      exact Fin.elim0 q
          · exact by
              constructor
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [2] [1, 2, 3] ∧ LexLE [1, 2, 3] [3, 2, 1])) h)
              · intro q
                exact Fin.elim0 q
    · exact by
        constructor
        · exact by
            intro h
            exact False.elim ((by decide : ¬ (LexLE [2] [1, 3] ∧ LexLE [1, 3] [3, 1])) h)
        · intro q
          fin_cases q
          · exact by
              constructor
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [2] [1, 3, 1] ∧ LexLE [1, 3, 1] [1, 3, 1])) h)
              · intro q
                fin_cases q
                · exact by
                    constructor
                    · exact by
                        intro h
                        exact False.elim ((by decide : ¬ (LexLE [2] [1, 3, 1, 1] ∧ LexLE [1, 3, 1, 1] [1, 1, 3, 1])) h)
                    · intro q
                      exact Fin.elim0 q
          · exact by
              constructor
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [2] [1, 3, 2] ∧ LexLE [1, 3, 2] [2, 3, 1])) h)
              · intro q
                exact Fin.elim0 q
    · exact by
        constructor
        · exact by
            intro h
            exact False.elim ((by decide : ¬ (LexLE [2] [1, 4] ∧ LexLE [1, 4] [4, 1])) h)
        · intro q
          fin_cases q
          · exact by
              constructor
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [2] [1, 4, 1] ∧ LexLE [1, 4, 1] [1, 4, 1])) h)
              · intro q
                exact Fin.elim0 q
    · exact by
        constructor
        · exact by
            intro h
            exact False.elim ((by decide : ¬ (LexLE [2] [1, 5] ∧ LexLE [1, 5] [5, 1])) h)
        · intro q
          exact Fin.elim0 q

private theorem k16t8_cover1333 : ∀ P ∈ pathPatterns 0 0 [2], HasCheckedCertificate 16 8 ([[2], [2], [2], [2]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k16t8p467, Certificates.k16t8p467_check⟩

private theorem k16t8_cover1332 : ∀ P ∈ pathPatterns 2 2 [2], HasCheckedCertificate 16 8 ([[2], [2], [2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [2] [] ∧ LexLE [] [])) h)
      · intro q
        fin_cases q
        · exact by
            intro h
            exact False.elim ((by decide : ¬ (LexLE [2] [1] ∧ LexLE [1] [1])) h)
        · exact by
            intro _
            exact k16t8_cover1333

private theorem k16t8_cover1334 : ∀ P ∈ pathPatterns 1 0 [2, 2], HasCheckedCertificate 16 8 ([[2], [2], [2, 2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [2, 2] [] ∧ LexLE [] [])) h)

private theorem k16t8_cover1335 : ∀ P ∈ pathPatterns 2 1 [3], HasCheckedCertificate 16 8 ([[2], [2], [3]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [3] [] ∧ LexLE [] [])) h)
      · intro q
        fin_cases q
        · exact by
            intro h
            exact False.elim ((by decide : ¬ (LexLE [3] [1] ∧ LexLE [1] [1])) h)

private theorem k16t8_cover1336 : ∀ P ∈ pathPatterns 2 0 [4], HasCheckedCertificate 16 8 ([[2], [2], [4]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [4] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k16t8_cover1331 : ∀ P ∈ pathPatterns 4 4 [2], HasCheckedCertificate 16 8 ([[2], [2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [2] [] ∧ LexLE [] [])) h)
      · intro q
        fin_cases q
        · exact by
            constructor
            · exact by
                intro h
                exact False.elim ((by decide : ¬ (LexLE [2] [1] ∧ LexLE [1] [1])) h)
            · intro q
              fin_cases q
              · exact by
                  constructor
                  · exact by
                      intro h
                      exact False.elim ((by decide : ¬ (LexLE [2] [1, 1] ∧ LexLE [1, 1] [1, 1])) h)
                  · intro q
                    fin_cases q
                    · exact by
                        intro h
                        exact False.elim ((by decide : ¬ (LexLE [2] [1, 1, 1] ∧ LexLE [1, 1, 1] [1, 1, 1])) h)
                    · exact by
                        intro h
                        exact False.elim ((by decide : ¬ (LexLE [2] [1, 1, 2] ∧ LexLE [1, 1, 2] [2, 1, 1])) h)
              · exact by
                  constructor
                  · exact by
                      intro h
                      exact False.elim ((by decide : ¬ (LexLE [2] [1, 2] ∧ LexLE [1, 2] [2, 1])) h)
                  · intro q
                    fin_cases q
                    · exact by
                        intro h
                        exact False.elim ((by decide : ¬ (LexLE [2] [1, 2, 1] ∧ LexLE [1, 2, 1] [1, 2, 1])) h)
              · exact by
                  constructor
                  · exact by
                      intro h
                      exact False.elim ((by decide : ¬ (LexLE [2] [1, 3] ∧ LexLE [1, 3] [3, 1])) h)
                  · intro q
                    exact Fin.elim0 q
        · exact by
            constructor
            · exact by
                intro _
                exact k16t8_cover1332
            · intro q
              fin_cases q
              · exact by
                  constructor
                  · exact by
                      intro h
                      exact False.elim ((by decide : ¬ (LexLE [2] [2, 1] ∧ LexLE [2, 1] [1, 2])) h)
                  · intro q
                    fin_cases q
                    · exact by
                        intro h
                        exact False.elim ((by decide : ¬ (LexLE [2] [2, 1, 1] ∧ LexLE [2, 1, 1] [1, 1, 2])) h)
              · exact by
                  constructor
                  · exact by
                      intro _
                      exact k16t8_cover1334
                  · intro q
                    exact Fin.elim0 q
        · exact by
            constructor
            · exact by
                intro _
                exact k16t8_cover1335
            · intro q
              fin_cases q
              · exact by
                  constructor
                  · exact by
                      intro h
                      exact False.elim ((by decide : ¬ (LexLE [2] [3, 1] ∧ LexLE [3, 1] [1, 3])) h)
                  · intro q
                    exact Fin.elim0 q
        · exact by
            constructor
            · exact by
                intro _
                exact k16t8_cover1336
            · intro q
              exact Fin.elim0 q

private theorem k16t8_cover1337 : ∀ P ∈ pathPatterns 1 0 [2, 1, 1, 2], HasCheckedCertificate 16 8 ([[2], [2, 1, 1, 2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [2, 1, 1, 2] [] ∧ LexLE [] [])) h)

private theorem k16t8_cover1338 : ∀ P ∈ pathPatterns 2 1 [2, 1, 2], HasCheckedCertificate 16 8 ([[2], [2, 1, 2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [2, 1, 2] [] ∧ LexLE [] [])) h)
      · intro q
        fin_cases q
        · exact by
            intro h
            exact False.elim ((by decide : ¬ (LexLE [2, 1, 2] [1] ∧ LexLE [1] [1])) h)

private theorem k16t8_cover1339 : ∀ P ∈ pathPatterns 2 0 [2, 1, 3], HasCheckedCertificate 16 8 ([[2], [2, 1, 3]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [2, 1, 3] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k16t8_cover1340 : ∀ P ∈ pathPatterns 3 2 [2, 2], HasCheckedCertificate 16 8 ([[2], [2, 2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [2, 2] [] ∧ LexLE [] [])) h)
      · intro q
        fin_cases q
        · exact by
            constructor
            · exact by
                intro h
                exact False.elim ((by decide : ¬ (LexLE [2, 2] [1] ∧ LexLE [1] [1])) h)
            · intro q
              fin_cases q
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [2, 2] [1, 1] ∧ LexLE [1, 1] [1, 1])) h)
        · exact by
            constructor
            · exact by
                intro h
                exact False.elim ((by decide : ¬ (LexLE [2, 2] [2] ∧ LexLE [2] [2])) h)
            · intro q
              exact Fin.elim0 q

private theorem k16t8_cover1341 : ∀ P ∈ pathPatterns 2 0 [2, 2, 2], HasCheckedCertificate 16 8 ([[2], [2, 2, 2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [2, 2, 2] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k16t8_cover1342 : ∀ P ∈ pathPatterns 3 1 [2, 3], HasCheckedCertificate 16 8 ([[2], [2, 3]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [2, 3] [] ∧ LexLE [] [])) h)
      · intro q
        fin_cases q
        · exact by
            constructor
            · exact by
                intro h
                exact False.elim ((by decide : ¬ (LexLE [2, 3] [1] ∧ LexLE [1] [1])) h)
            · intro q
              exact Fin.elim0 q

private theorem k16t8_cover1343 : ∀ P ∈ pathPatterns 3 0 [2, 4], HasCheckedCertificate 16 8 ([[2], [2, 4]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [2, 4] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k16t8_cover1345 : ∀ P ∈ pathPatterns 2 0 [3], HasCheckedCertificate 16 8 ([[2], [3], [3]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [3] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k16t8_cover1344 : ∀ P ∈ pathPatterns 4 3 [3], HasCheckedCertificate 16 8 ([[2], [3]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [3] [] ∧ LexLE [] [])) h)
      · intro q
        fin_cases q
        · exact by
            constructor
            · exact by
                intro h
                exact False.elim ((by decide : ¬ (LexLE [3] [1] ∧ LexLE [1] [1])) h)
            · intro q
              fin_cases q
              · exact by
                  constructor
                  · exact by
                      intro h
                      exact False.elim ((by decide : ¬ (LexLE [3] [1, 1] ∧ LexLE [1, 1] [1, 1])) h)
                  · intro q
                    fin_cases q
                    · exact by
                        intro h
                        exact False.elim ((by decide : ¬ (LexLE [3] [1, 1, 1] ∧ LexLE [1, 1, 1] [1, 1, 1])) h)
              · exact by
                  constructor
                  · exact by
                      intro h
                      exact False.elim ((by decide : ¬ (LexLE [3] [1, 2] ∧ LexLE [1, 2] [2, 1])) h)
                  · intro q
                    exact Fin.elim0 q
        · exact by
            constructor
            · exact by
                intro h
                exact False.elim ((by decide : ¬ (LexLE [3] [2] ∧ LexLE [2] [2])) h)
            · intro q
              fin_cases q
              · exact by
                  constructor
                  · exact by
                      intro h
                      exact False.elim ((by decide : ¬ (LexLE [3] [2, 1] ∧ LexLE [2, 1] [1, 2])) h)
                  · intro q
                    exact Fin.elim0 q
        · exact by
            constructor
            · exact by
                intro _
                exact k16t8_cover1345
            · intro q
              exact Fin.elim0 q

private theorem k16t8_cover1346 : ∀ P ∈ pathPatterns 3 0 [3, 3], HasCheckedCertificate 16 8 ([[2], [3, 3]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [3, 3] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k16t8_cover1347 : ∀ P ∈ pathPatterns 4 2 [4], HasCheckedCertificate 16 8 ([[2], [4]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [4] [] ∧ LexLE [] [])) h)
      · intro q
        fin_cases q
        · exact by
            constructor
            · exact by
                intro h
                exact False.elim ((by decide : ¬ (LexLE [4] [1] ∧ LexLE [1] [1])) h)
            · intro q
              fin_cases q
              · exact by
                  constructor
                  · exact by
                      intro h
                      exact False.elim ((by decide : ¬ (LexLE [4] [1, 1] ∧ LexLE [1, 1] [1, 1])) h)
                  · intro q
                    exact Fin.elim0 q
        · exact by
            constructor
            · exact by
                intro h
                exact False.elim ((by decide : ¬ (LexLE [4] [2] ∧ LexLE [2] [2])) h)
            · intro q
              exact Fin.elim0 q

private theorem k16t8_cover1348 : ∀ P ∈ pathPatterns 4 1 [5], HasCheckedCertificate 16 8 ([[2], [5]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [5] [] ∧ LexLE [] [])) h)
      · intro q
        fin_cases q
        · exact by
            constructor
            · exact by
                intro h
                exact False.elim ((by decide : ¬ (LexLE [5] [1] ∧ LexLE [1] [1])) h)
            · intro q
              exact Fin.elim0 q

private theorem k16t8_cover1349 : ∀ P ∈ pathPatterns 4 0 [6], HasCheckedCertificate 16 8 ([[2], [6]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [6] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k16t8_seq1329 : amountSequenceForall 5 6 (fun tail =>
    (LexLE [2] ([] ++ tail) ∧ LexLE ([] ++ tail) ([] ++ tail).reverse) →
    ∀ P ∈ pathPatterns (5 - ([] ++ tail).length) (6 - ([] ++ tail).sum) ([] ++ tail),
      HasCheckedCertificate 16 8 ([[2]] ++ (([] ++ tail) :: P))) :=
by
  constructor
  · exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [2] [] ∧ LexLE [] [])) h)
  · intro q
    fin_cases q
    · exact k16t8_seq1330

    · exact by
        constructor
        · exact by
            intro _
            exact k16t8_cover1331
        · intro q
          fin_cases q
          · exact by
              constructor
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [2] [2, 1] ∧ LexLE [2, 1] [1, 2])) h)
              · intro q
                fin_cases q
                · exact by
                    constructor
                    · exact by
                        intro h
                        exact False.elim ((by decide : ¬ (LexLE [2] [2, 1, 1] ∧ LexLE [2, 1, 1] [1, 1, 2])) h)
                    · intro q
                      fin_cases q
                      · exact by
                          constructor
                          · exact by
                              intro h
                              exact False.elim ((by decide : ¬ (LexLE [2] [2, 1, 1, 1] ∧ LexLE [2, 1, 1, 1] [1, 1, 1, 2])) h)
                          · intro q
                            fin_cases q
                            · exact by
                                intro h
                                exact False.elim ((by decide : ¬ (LexLE [2] [2, 1, 1, 1, 1] ∧ LexLE [2, 1, 1, 1, 1] [1, 1, 1, 1, 2])) h)
                      · exact by
                          constructor
                          · exact by
                              intro _
                              exact k16t8_cover1337
                          · intro q
                            exact Fin.elim0 q
                · exact by
                    constructor
                    · exact by
                        intro _
                        exact k16t8_cover1338
                    · intro q
                      fin_cases q
                      · exact by
                          constructor
                          · exact by
                              intro h
                              exact False.elim ((by decide : ¬ (LexLE [2] [2, 1, 2, 1] ∧ LexLE [2, 1, 2, 1] [1, 2, 1, 2])) h)
                          · intro q
                            exact Fin.elim0 q
                · exact by
                    constructor
                    · exact by
                        intro _
                        exact k16t8_cover1339
                    · intro q
                      exact Fin.elim0 q
          · exact by
              constructor
              · exact by
                  intro _
                  exact k16t8_cover1340
              · intro q
                fin_cases q
                · exact by
                    constructor
                    · exact by
                        intro h
                        exact False.elim ((by decide : ¬ (LexLE [2] [2, 2, 1] ∧ LexLE [2, 2, 1] [1, 2, 2])) h)
                    · intro q
                      fin_cases q
                      · exact by
                          constructor
                          · exact by
                              intro h
                              exact False.elim ((by decide : ¬ (LexLE [2] [2, 2, 1, 1] ∧ LexLE [2, 2, 1, 1] [1, 1, 2, 2])) h)
                          · intro q
                            exact Fin.elim0 q
                · exact by
                    constructor
                    · exact by
                        intro _
                        exact k16t8_cover1341
                    · intro q
                      exact Fin.elim0 q
          · exact by
              constructor
              · exact by
                  intro _
                  exact k16t8_cover1342
              · intro q
                fin_cases q
                · exact by
                    constructor
                    · exact by
                        intro h
                        exact False.elim ((by decide : ¬ (LexLE [2] [2, 3, 1] ∧ LexLE [2, 3, 1] [1, 3, 2])) h)
                    · intro q
                      exact Fin.elim0 q
          · exact by
              constructor
              · exact by
                  intro _
                  exact k16t8_cover1343
              · intro q
                exact Fin.elim0 q
    · exact by
        constructor
        · exact by
            intro _
            exact k16t8_cover1344
        · intro q
          fin_cases q
          · exact by
              constructor
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [2] [3, 1] ∧ LexLE [3, 1] [1, 3])) h)
              · intro q
                fin_cases q
                · exact by
                    constructor
                    · exact by
                        intro h
                        exact False.elim ((by decide : ¬ (LexLE [2] [3, 1, 1] ∧ LexLE [3, 1, 1] [1, 1, 3])) h)
                    · intro q
                      fin_cases q
                      · exact by
                          constructor
                          · exact by
                              intro h
                              exact False.elim ((by decide : ¬ (LexLE [2] [3, 1, 1, 1] ∧ LexLE [3, 1, 1, 1] [1, 1, 1, 3])) h)
                          · intro q
                            exact Fin.elim0 q
                · exact by
                    constructor
                    · exact by
                        intro h
                        exact False.elim ((by decide : ¬ (LexLE [2] [3, 1, 2] ∧ LexLE [3, 1, 2] [2, 1, 3])) h)
                    · intro q
                      exact Fin.elim0 q
          · exact by
              constructor
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [2] [3, 2] ∧ LexLE [3, 2] [2, 3])) h)
              · intro q
                fin_cases q
                · exact by
                    constructor
                    · exact by
                        intro h
                        exact False.elim ((by decide : ¬ (LexLE [2] [3, 2, 1] ∧ LexLE [3, 2, 1] [1, 2, 3])) h)
                    · intro q
                      exact Fin.elim0 q
          · exact by
              constructor
              · exact by
                  intro _
                  exact k16t8_cover1346
              · intro q
                exact Fin.elim0 q
    · exact by
        constructor
        · exact by
            intro _
            exact k16t8_cover1347
        · intro q
          fin_cases q
          · exact by
              constructor
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [2] [4, 1] ∧ LexLE [4, 1] [1, 4])) h)
              · intro q
                fin_cases q
                · exact by
                    constructor
                    · exact by
                        intro h
                        exact False.elim ((by decide : ¬ (LexLE [2] [4, 1, 1] ∧ LexLE [4, 1, 1] [1, 1, 4])) h)
                    · intro q
                      exact Fin.elim0 q
          · exact by
              constructor
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [2] [4, 2] ∧ LexLE [4, 2] [2, 4])) h)
              · intro q
                exact Fin.elim0 q
    · exact by
        constructor
        · exact by
            intro _
            exact k16t8_cover1348
        · intro q
          fin_cases q
          · exact by
              constructor
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [2] [5, 1] ∧ LexLE [5, 1] [1, 5])) h)
              · intro q
                exact Fin.elim0 q
    · exact by
        constructor
        · exact by
            intro _
            exact k16t8_cover1349
        · intro q
          exact Fin.elim0 q

private theorem k16t8_cover1328 : ∀ P ∈ pathPatterns 6 6 [2], HasCheckedCertificate 16 8 ([[2]] ++ P) := by
  apply pathPatterns_forall_step
  exact k16t8_seq1329


private theorem k16t8_cover1351 : ∀ P ∈ pathPatterns 1 0 [2, 1, 1, 1, 1, 2], HasCheckedCertificate 16 8 ([[2, 1, 1, 1, 1, 2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [2, 1, 1, 1, 1, 2] [] ∧ LexLE [] [])) h)

private theorem k16t8_cover1352 : ∀ P ∈ pathPatterns 2 1 [2, 1, 1, 1, 2], HasCheckedCertificate 16 8 ([[2, 1, 1, 1, 2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [2, 1, 1, 1, 2] [] ∧ LexLE [] [])) h)
      · intro q
        fin_cases q
        · exact by
            intro h
            exact False.elim ((by decide : ¬ (LexLE [2, 1, 1, 1, 2] [1] ∧ LexLE [1] [1])) h)

private theorem k16t8_cover1353 : ∀ P ∈ pathPatterns 2 0 [2, 1, 1, 1, 3], HasCheckedCertificate 16 8 ([[2, 1, 1, 1, 3]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [2, 1, 1, 1, 3] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k16t8_cover1354 : ∀ P ∈ pathPatterns 3 2 [2, 1, 1, 2], HasCheckedCertificate 16 8 ([[2, 1, 1, 2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [2, 1, 1, 2] [] ∧ LexLE [] [])) h)
      · intro q
        fin_cases q
        · exact by
            constructor
            · exact by
                intro h
                exact False.elim ((by decide : ¬ (LexLE [2, 1, 1, 2] [1] ∧ LexLE [1] [1])) h)
            · intro q
              fin_cases q
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [2, 1, 1, 2] [1, 1] ∧ LexLE [1, 1] [1, 1])) h)
        · exact by
            constructor
            · exact by
                intro h
                exact False.elim ((by decide : ¬ (LexLE [2, 1, 1, 2] [2] ∧ LexLE [2] [2])) h)
            · intro q
              exact Fin.elim0 q

private theorem k16t8_cover1355 : ∀ P ∈ pathPatterns 2 0 [2, 1, 1, 2, 2], HasCheckedCertificate 16 8 ([[2, 1, 1, 2, 2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [2, 1, 1, 2, 2] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k16t8_cover1356 : ∀ P ∈ pathPatterns 3 1 [2, 1, 1, 3], HasCheckedCertificate 16 8 ([[2, 1, 1, 3]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [2, 1, 1, 3] [] ∧ LexLE [] [])) h)
      · intro q
        fin_cases q
        · exact by
            constructor
            · exact by
                intro h
                exact False.elim ((by decide : ¬ (LexLE [2, 1, 1, 3] [1] ∧ LexLE [1] [1])) h)
            · intro q
              exact Fin.elim0 q

private theorem k16t8_cover1357 : ∀ P ∈ pathPatterns 3 0 [2, 1, 1, 4], HasCheckedCertificate 16 8 ([[2, 1, 1, 4]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [2, 1, 1, 4] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k16t8_cover1359 : ∀ P ∈ pathPatterns 2 0 [3], HasCheckedCertificate 16 8 ([[2, 1, 2], [3]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [3] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k16t8_cover1358 : ∀ P ∈ pathPatterns 4 3 [2, 1, 2], HasCheckedCertificate 16 8 ([[2, 1, 2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [2, 1, 2] [] ∧ LexLE [] [])) h)
      · intro q
        fin_cases q
        · exact by
            constructor
            · exact by
                intro h
                exact False.elim ((by decide : ¬ (LexLE [2, 1, 2] [1] ∧ LexLE [1] [1])) h)
            · intro q
              fin_cases q
              · exact by
                  constructor
                  · exact by
                      intro h
                      exact False.elim ((by decide : ¬ (LexLE [2, 1, 2] [1, 1] ∧ LexLE [1, 1] [1, 1])) h)
                  · intro q
                    fin_cases q
                    · exact by
                        intro h
                        exact False.elim ((by decide : ¬ (LexLE [2, 1, 2] [1, 1, 1] ∧ LexLE [1, 1, 1] [1, 1, 1])) h)
              · exact by
                  constructor
                  · exact by
                      intro h
                      exact False.elim ((by decide : ¬ (LexLE [2, 1, 2] [1, 2] ∧ LexLE [1, 2] [2, 1])) h)
                  · intro q
                    exact Fin.elim0 q
        · exact by
            constructor
            · exact by
                intro h
                exact False.elim ((by decide : ¬ (LexLE [2, 1, 2] [2] ∧ LexLE [2] [2])) h)
            · intro q
              fin_cases q
              · exact by
                  constructor
                  · exact by
                      intro h
                      exact False.elim ((by decide : ¬ (LexLE [2, 1, 2] [2, 1] ∧ LexLE [2, 1] [1, 2])) h)
                  · intro q
                    exact Fin.elim0 q
        · exact by
            constructor
            · exact by
                intro _
                exact k16t8_cover1359
            · intro q
              exact Fin.elim0 q

private theorem k16t8_cover1360 : ∀ P ∈ pathPatterns 2 0 [2, 1, 2, 1, 2], HasCheckedCertificate 16 8 ([[2, 1, 2, 1, 2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [2, 1, 2, 1, 2] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k16t8_cover1361 : ∀ P ∈ pathPatterns 3 1 [2, 1, 2, 2], HasCheckedCertificate 16 8 ([[2, 1, 2, 2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [2, 1, 2, 2] [] ∧ LexLE [] [])) h)
      · intro q
        fin_cases q
        · exact by
            constructor
            · exact by
                intro h
                exact False.elim ((by decide : ¬ (LexLE [2, 1, 2, 2] [1] ∧ LexLE [1] [1])) h)
            · intro q
              exact Fin.elim0 q

private theorem k16t8_cover1362 : ∀ P ∈ pathPatterns 3 0 [2, 1, 2, 3], HasCheckedCertificate 16 8 ([[2, 1, 2, 3]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [2, 1, 2, 3] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k16t8_cover1363 : ∀ P ∈ pathPatterns 4 2 [2, 1, 3], HasCheckedCertificate 16 8 ([[2, 1, 3]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [2, 1, 3] [] ∧ LexLE [] [])) h)
      · intro q
        fin_cases q
        · exact by
            constructor
            · exact by
                intro h
                exact False.elim ((by decide : ¬ (LexLE [2, 1, 3] [1] ∧ LexLE [1] [1])) h)
            · intro q
              fin_cases q
              · exact by
                  constructor
                  · exact by
                      intro h
                      exact False.elim ((by decide : ¬ (LexLE [2, 1, 3] [1, 1] ∧ LexLE [1, 1] [1, 1])) h)
                  · intro q
                    exact Fin.elim0 q
        · exact by
            constructor
            · exact by
                intro h
                exact False.elim ((by decide : ¬ (LexLE [2, 1, 3] [2] ∧ LexLE [2] [2])) h)
            · intro q
              exact Fin.elim0 q

private theorem k16t8_cover1364 : ∀ P ∈ pathPatterns 3 0 [2, 1, 3, 2], HasCheckedCertificate 16 8 ([[2, 1, 3, 2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [2, 1, 3, 2] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k16t8_cover1365 : ∀ P ∈ pathPatterns 4 1 [2, 1, 4], HasCheckedCertificate 16 8 ([[2, 1, 4]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [2, 1, 4] [] ∧ LexLE [] [])) h)
      · intro q
        fin_cases q
        · exact by
            constructor
            · exact by
                intro h
                exact False.elim ((by decide : ¬ (LexLE [2, 1, 4] [1] ∧ LexLE [1] [1])) h)
            · intro q
              exact Fin.elim0 q

private theorem k16t8_cover1366 : ∀ P ∈ pathPatterns 4 0 [2, 1, 5], HasCheckedCertificate 16 8 ([[2, 1, 5]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [2, 1, 5] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k16t8_seq1350 : amountSequenceForall 5 5 (fun tail =>
    (LexLE [] ([2, 1] ++ tail) ∧ LexLE ([2, 1] ++ tail) ([2, 1] ++ tail).reverse) →
    ∀ P ∈ pathPatterns (7 - ([2, 1] ++ tail).length) (8 - ([2, 1] ++ tail).sum) ([2, 1] ++ tail),
      HasCheckedCertificate 16 8 ([] ++ (([2, 1] ++ tail) :: P))) :=
by
  constructor
  · exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [] [2, 1] ∧ LexLE [2, 1] [1, 2])) h)
  · intro q
    fin_cases q
    · exact by
        constructor
        · exact by
            intro h
            exact False.elim ((by decide : ¬ (LexLE [] [2, 1, 1] ∧ LexLE [2, 1, 1] [1, 1, 2])) h)
        · intro q
          fin_cases q
          · exact by
              constructor
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [] [2, 1, 1, 1] ∧ LexLE [2, 1, 1, 1] [1, 1, 1, 2])) h)
              · intro q
                fin_cases q
                · exact by
                    constructor
                    · exact by
                        intro h
                        exact False.elim ((by decide : ¬ (LexLE [] [2, 1, 1, 1, 1] ∧ LexLE [2, 1, 1, 1, 1] [1, 1, 1, 1, 2])) h)
                    · intro q
                      fin_cases q
                      · exact by
                          constructor
                          · exact by
                              intro h
                              exact False.elim ((by decide : ¬ (LexLE [] [2, 1, 1, 1, 1, 1] ∧ LexLE [2, 1, 1, 1, 1, 1] [1, 1, 1, 1, 1, 2])) h)
                          · intro q
                            fin_cases q
                            · exact by
                                intro h
                                exact False.elim ((by decide : ¬ (LexLE [] [2, 1, 1, 1, 1, 1, 1] ∧ LexLE [2, 1, 1, 1, 1, 1, 1] [1, 1, 1, 1, 1, 1, 2])) h)
                      · exact by
                          constructor
                          · exact by
                              intro _
                              exact k16t8_cover1351
                          · intro q
                            exact Fin.elim0 q
                · exact by
                    constructor
                    · exact by
                        intro _
                        exact k16t8_cover1352
                    · intro q
                      fin_cases q
                      · exact by
                          constructor
                          · exact by
                              intro h
                              exact False.elim ((by decide : ¬ (LexLE [] [2, 1, 1, 1, 2, 1] ∧ LexLE [2, 1, 1, 1, 2, 1] [1, 2, 1, 1, 1, 2])) h)
                          · intro q
                            exact Fin.elim0 q
                · exact by
                    constructor
                    · exact by
                        intro _
                        exact k16t8_cover1353
                    · intro q
                      exact Fin.elim0 q
          · exact by
              constructor
              · exact by
                  intro _
                  exact k16t8_cover1354
              · intro q
                fin_cases q
                · exact by
                    constructor
                    · exact by
                        intro h
                        exact False.elim ((by decide : ¬ (LexLE [] [2, 1, 1, 2, 1] ∧ LexLE [2, 1, 1, 2, 1] [1, 2, 1, 1, 2])) h)
                    · intro q
                      fin_cases q
                      · exact by
                          constructor
                          · exact by
                              intro h
                              exact False.elim ((by decide : ¬ (LexLE [] [2, 1, 1, 2, 1, 1] ∧ LexLE [2, 1, 1, 2, 1, 1] [1, 1, 2, 1, 1, 2])) h)
                          · intro q
                            exact Fin.elim0 q
                · exact by
                    constructor
                    · exact by
                        intro _
                        exact k16t8_cover1355
                    · intro q
                      exact Fin.elim0 q
          · exact by
              constructor
              · exact by
                  intro _
                  exact k16t8_cover1356
              · intro q
                fin_cases q
                · exact by
                    constructor
                    · exact by
                        intro h
                        exact False.elim ((by decide : ¬ (LexLE [] [2, 1, 1, 3, 1] ∧ LexLE [2, 1, 1, 3, 1] [1, 3, 1, 1, 2])) h)
                    · intro q
                      exact Fin.elim0 q
          · exact by
              constructor
              · exact by
                  intro _
                  exact k16t8_cover1357
              · intro q
                exact Fin.elim0 q
    · exact by
        constructor
        · exact by
            intro _
            exact k16t8_cover1358
        · intro q
          fin_cases q
          · exact by
              constructor
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [] [2, 1, 2, 1] ∧ LexLE [2, 1, 2, 1] [1, 2, 1, 2])) h)
              · intro q
                fin_cases q
                · exact by
                    constructor
                    · exact by
                        intro h
                        exact False.elim ((by decide : ¬ (LexLE [] [2, 1, 2, 1, 1] ∧ LexLE [2, 1, 2, 1, 1] [1, 1, 2, 1, 2])) h)
                    · intro q
                      fin_cases q
                      · exact by
                          constructor
                          · exact by
                              intro h
                              exact False.elim ((by decide : ¬ (LexLE [] [2, 1, 2, 1, 1, 1] ∧ LexLE [2, 1, 2, 1, 1, 1] [1, 1, 1, 2, 1, 2])) h)
                          · intro q
                            exact Fin.elim0 q
                · exact by
                    constructor
                    · exact by
                        intro _
                        exact k16t8_cover1360
                    · intro q
                      exact Fin.elim0 q
          · exact by
              constructor
              · exact by
                  intro _
                  exact k16t8_cover1361
              · intro q
                fin_cases q
                · exact by
                    constructor
                    · exact by
                        intro h
                        exact False.elim ((by decide : ¬ (LexLE [] [2, 1, 2, 2, 1] ∧ LexLE [2, 1, 2, 2, 1] [1, 2, 2, 1, 2])) h)
                    · intro q
                      exact Fin.elim0 q
          · exact by
              constructor
              · exact by
                  intro _
                  exact k16t8_cover1362
              · intro q
                exact Fin.elim0 q
    · exact by
        constructor
        · exact by
            intro _
            exact k16t8_cover1363
        · intro q
          fin_cases q
          · exact by
              constructor
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [] [2, 1, 3, 1] ∧ LexLE [2, 1, 3, 1] [1, 3, 1, 2])) h)
              · intro q
                fin_cases q
                · exact by
                    constructor
                    · exact by
                        intro h
                        exact False.elim ((by decide : ¬ (LexLE [] [2, 1, 3, 1, 1] ∧ LexLE [2, 1, 3, 1, 1] [1, 1, 3, 1, 2])) h)
                    · intro q
                      exact Fin.elim0 q
          · exact by
              constructor
              · exact by
                  intro _
                  exact k16t8_cover1364
              · intro q
                exact Fin.elim0 q
    · exact by
        constructor
        · exact by
            intro _
            exact k16t8_cover1365
        · intro q
          fin_cases q
          · exact by
              constructor
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [] [2, 1, 4, 1] ∧ LexLE [2, 1, 4, 1] [1, 4, 1, 2])) h)
              · intro q
                exact Fin.elim0 q
    · exact by
        constructor
        · exact by
            intro _
            exact k16t8_cover1366
        · intro q
          exact Fin.elim0 q

private theorem k16t8_cover1368 : ∀ P ∈ pathPatterns 2 0 [2, 2], HasCheckedCertificate 16 8 ([[2, 2], [2, 2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [2, 2] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k16t8_cover1369 : ∀ P ∈ pathPatterns 3 1 [3], HasCheckedCertificate 16 8 ([[2, 2], [3]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [3] [] ∧ LexLE [] [])) h)
      · intro q
        fin_cases q
        · exact by
            constructor
            · exact by
                intro h
                exact False.elim ((by decide : ¬ (LexLE [3] [1] ∧ LexLE [1] [1])) h)
            · intro q
              exact Fin.elim0 q

private theorem k16t8_cover1370 : ∀ P ∈ pathPatterns 3 0 [4], HasCheckedCertificate 16 8 ([[2, 2], [4]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [4] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k16t8_cover1367 : ∀ P ∈ pathPatterns 5 4 [2, 2], HasCheckedCertificate 16 8 ([[2, 2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [2, 2] [] ∧ LexLE [] [])) h)
      · intro q
        fin_cases q
        · exact by
            constructor
            · exact by
                intro h
                exact False.elim ((by decide : ¬ (LexLE [2, 2] [1] ∧ LexLE [1] [1])) h)
            · intro q
              fin_cases q
              · exact by
                  constructor
                  · exact by
                      intro h
                      exact False.elim ((by decide : ¬ (LexLE [2, 2] [1, 1] ∧ LexLE [1, 1] [1, 1])) h)
                  · intro q
                    fin_cases q
                    · exact by
                        constructor
                        · exact by
                            intro h
                            exact False.elim ((by decide : ¬ (LexLE [2, 2] [1, 1, 1] ∧ LexLE [1, 1, 1] [1, 1, 1])) h)
                        · intro q
                          fin_cases q
                          · exact by
                              intro h
                              exact False.elim ((by decide : ¬ (LexLE [2, 2] [1, 1, 1, 1] ∧ LexLE [1, 1, 1, 1] [1, 1, 1, 1])) h)
                    · exact by
                        constructor
                        · exact by
                            intro h
                            exact False.elim ((by decide : ¬ (LexLE [2, 2] [1, 1, 2] ∧ LexLE [1, 1, 2] [2, 1, 1])) h)
                        · intro q
                          exact Fin.elim0 q
              · exact by
                  constructor
                  · exact by
                      intro h
                      exact False.elim ((by decide : ¬ (LexLE [2, 2] [1, 2] ∧ LexLE [1, 2] [2, 1])) h)
                  · intro q
                    fin_cases q
                    · exact by
                        constructor
                        · exact by
                            intro h
                            exact False.elim ((by decide : ¬ (LexLE [2, 2] [1, 2, 1] ∧ LexLE [1, 2, 1] [1, 2, 1])) h)
                        · intro q
                          exact Fin.elim0 q
              · exact by
                  constructor
                  · exact by
                      intro h
                      exact False.elim ((by decide : ¬ (LexLE [2, 2] [1, 3] ∧ LexLE [1, 3] [3, 1])) h)
                  · intro q
                    exact Fin.elim0 q
        · exact by
            constructor
            · exact by
                intro h
                exact False.elim ((by decide : ¬ (LexLE [2, 2] [2] ∧ LexLE [2] [2])) h)
            · intro q
              fin_cases q
              · exact by
                  constructor
                  · exact by
                      intro h
                      exact False.elim ((by decide : ¬ (LexLE [2, 2] [2, 1] ∧ LexLE [2, 1] [1, 2])) h)
                  · intro q
                    fin_cases q
                    · exact by
                        constructor
                        · exact by
                            intro h
                            exact False.elim ((by decide : ¬ (LexLE [2, 2] [2, 1, 1] ∧ LexLE [2, 1, 1] [1, 1, 2])) h)
                        · intro q
                          exact Fin.elim0 q
              · exact by
                  constructor
                  · exact by
                      intro _
                      exact k16t8_cover1368
                  · intro q
                    exact Fin.elim0 q
        · exact by
            constructor
            · exact by
                intro _
                exact k16t8_cover1369
            · intro q
              fin_cases q
              · exact by
                  constructor
                  · exact by
                      intro h
                      exact False.elim ((by decide : ¬ (LexLE [2, 2] [3, 1] ∧ LexLE [3, 1] [1, 3])) h)
                  · intro q
                    exact Fin.elim0 q
        · exact by
            constructor
            · exact by
                intro _
                exact k16t8_cover1370
            · intro q
              exact Fin.elim0 q

private theorem k16t8_cover1371 : ∀ P ∈ pathPatterns 3 0 [2, 2, 1, 3], HasCheckedCertificate 16 8 ([[2, 2, 1, 3]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [2, 2, 1, 3] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k16t8_cover1372 : ∀ P ∈ pathPatterns 4 2 [2, 2, 2], HasCheckedCertificate 16 8 ([[2, 2, 2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [2, 2, 2] [] ∧ LexLE [] [])) h)
      · intro q
        fin_cases q
        · exact by
            constructor
            · exact by
                intro h
                exact False.elim ((by decide : ¬ (LexLE [2, 2, 2] [1] ∧ LexLE [1] [1])) h)
            · intro q
              fin_cases q
              · exact by
                  constructor
                  · exact by
                      intro h
                      exact False.elim ((by decide : ¬ (LexLE [2, 2, 2] [1, 1] ∧ LexLE [1, 1] [1, 1])) h)
                  · intro q
                    exact Fin.elim0 q
        · exact by
            constructor
            · exact by
                intro h
                exact False.elim ((by decide : ¬ (LexLE [2, 2, 2] [2] ∧ LexLE [2] [2])) h)
            · intro q
              exact Fin.elim0 q

private theorem k16t8_cover1373 : ∀ P ∈ pathPatterns 3 0 [2, 2, 2, 2], HasCheckedCertificate 16 8 ([[2, 2, 2, 2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [2, 2, 2, 2] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k16t8_cover1374 : ∀ P ∈ pathPatterns 4 1 [2, 2, 3], HasCheckedCertificate 16 8 ([[2, 2, 3]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [2, 2, 3] [] ∧ LexLE [] [])) h)
      · intro q
        fin_cases q
        · exact by
            constructor
            · exact by
                intro h
                exact False.elim ((by decide : ¬ (LexLE [2, 2, 3] [1] ∧ LexLE [1] [1])) h)
            · intro q
              exact Fin.elim0 q

private theorem k16t8_cover1375 : ∀ P ∈ pathPatterns 4 0 [2, 2, 4], HasCheckedCertificate 16 8 ([[2, 2, 4]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [2, 2, 4] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k16t8_cover1377 : ∀ P ∈ pathPatterns 3 0 [3], HasCheckedCertificate 16 8 ([[2, 3], [3]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [3] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k16t8_cover1376 : ∀ P ∈ pathPatterns 5 3 [2, 3], HasCheckedCertificate 16 8 ([[2, 3]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [2, 3] [] ∧ LexLE [] [])) h)
      · intro q
        fin_cases q
        · exact by
            constructor
            · exact by
                intro h
                exact False.elim ((by decide : ¬ (LexLE [2, 3] [1] ∧ LexLE [1] [1])) h)
            · intro q
              fin_cases q
              · exact by
                  constructor
                  · exact by
                      intro h
                      exact False.elim ((by decide : ¬ (LexLE [2, 3] [1, 1] ∧ LexLE [1, 1] [1, 1])) h)
                  · intro q
                    fin_cases q
                    · exact by
                        constructor
                        · exact by
                            intro h
                            exact False.elim ((by decide : ¬ (LexLE [2, 3] [1, 1, 1] ∧ LexLE [1, 1, 1] [1, 1, 1])) h)
                        · intro q
                          exact Fin.elim0 q
              · exact by
                  constructor
                  · exact by
                      intro h
                      exact False.elim ((by decide : ¬ (LexLE [2, 3] [1, 2] ∧ LexLE [1, 2] [2, 1])) h)
                  · intro q
                    exact Fin.elim0 q
        · exact by
            constructor
            · exact by
                intro h
                exact False.elim ((by decide : ¬ (LexLE [2, 3] [2] ∧ LexLE [2] [2])) h)
            · intro q
              fin_cases q
              · exact by
                  constructor
                  · exact by
                      intro h
                      exact False.elim ((by decide : ¬ (LexLE [2, 3] [2, 1] ∧ LexLE [2, 1] [1, 2])) h)
                  · intro q
                    exact Fin.elim0 q
        · exact by
            constructor
            · exact by
                intro _
                exact k16t8_cover1377
            · intro q
              exact Fin.elim0 q

private theorem k16t8_cover1378 : ∀ P ∈ pathPatterns 4 1 [2, 3, 2], HasCheckedCertificate 16 8 ([[2, 3, 2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [2, 3, 2] [] ∧ LexLE [] [])) h)
      · intro q
        fin_cases q
        · exact by
            constructor
            · exact by
                intro h
                exact False.elim ((by decide : ¬ (LexLE [2, 3, 2] [1] ∧ LexLE [1] [1])) h)
            · intro q
              exact Fin.elim0 q

private theorem k16t8_cover1379 : ∀ P ∈ pathPatterns 4 0 [2, 3, 3], HasCheckedCertificate 16 8 ([[2, 3, 3]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [2, 3, 3] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k16t8_cover1380 : ∀ P ∈ pathPatterns 5 2 [2, 4], HasCheckedCertificate 16 8 ([[2, 4]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [2, 4] [] ∧ LexLE [] [])) h)
      · intro q
        fin_cases q
        · exact by
            constructor
            · exact by
                intro h
                exact False.elim ((by decide : ¬ (LexLE [2, 4] [1] ∧ LexLE [1] [1])) h)
            · intro q
              fin_cases q
              · exact by
                  constructor
                  · exact by
                      intro h
                      exact False.elim ((by decide : ¬ (LexLE [2, 4] [1, 1] ∧ LexLE [1, 1] [1, 1])) h)
                  · intro q
                    exact Fin.elim0 q
        · exact by
            constructor
            · exact by
                intro h
                exact False.elim ((by decide : ¬ (LexLE [2, 4] [2] ∧ LexLE [2] [2])) h)
            · intro q
              exact Fin.elim0 q

private theorem k16t8_cover1381 : ∀ P ∈ pathPatterns 4 0 [2, 4, 2], HasCheckedCertificate 16 8 ([[2, 4, 2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [2, 4, 2] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k16t8_cover1382 : ∀ P ∈ pathPatterns 5 1 [2, 5], HasCheckedCertificate 16 8 ([[2, 5]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [2, 5] [] ∧ LexLE [] [])) h)
      · intro q
        fin_cases q
        · exact by
            constructor
            · exact by
                intro h
                exact False.elim ((by decide : ¬ (LexLE [2, 5] [1] ∧ LexLE [1] [1])) h)
            · intro q
              exact Fin.elim0 q

private theorem k16t8_cover1383 : ∀ P ∈ pathPatterns 5 0 [2, 6], HasCheckedCertificate 16 8 ([[2, 6]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [2, 6] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k16t8_seq1327 : amountSequenceForall 6 6 (fun tail =>
    (LexLE [] ([2] ++ tail) ∧ LexLE ([2] ++ tail) ([2] ++ tail).reverse) →
    ∀ P ∈ pathPatterns (7 - ([2] ++ tail).length) (8 - ([2] ++ tail).sum) ([2] ++ tail),
      HasCheckedCertificate 16 8 ([] ++ (([2] ++ tail) :: P))) :=
by
  constructor
  · exact by
      intro _
      exact k16t8_cover1328
  · intro q
    fin_cases q
    · exact k16t8_seq1350

    · exact by
        constructor
        · exact by
            intro _
            exact k16t8_cover1367
        · intro q
          fin_cases q
          · exact by
              constructor
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [] [2, 2, 1] ∧ LexLE [2, 2, 1] [1, 2, 2])) h)
              · intro q
                fin_cases q
                · exact by
                    constructor
                    · exact by
                        intro h
                        exact False.elim ((by decide : ¬ (LexLE [] [2, 2, 1, 1] ∧ LexLE [2, 2, 1, 1] [1, 1, 2, 2])) h)
                    · intro q
                      fin_cases q
                      · exact by
                          constructor
                          · exact by
                              intro h
                              exact False.elim ((by decide : ¬ (LexLE [] [2, 2, 1, 1, 1] ∧ LexLE [2, 2, 1, 1, 1] [1, 1, 1, 2, 2])) h)
                          · intro q
                            fin_cases q
                            · exact by
                                constructor
                                · exact by
                                    intro h
                                    exact False.elim ((by decide : ¬ (LexLE [] [2, 2, 1, 1, 1, 1] ∧ LexLE [2, 2, 1, 1, 1, 1] [1, 1, 1, 1, 2, 2])) h)
                                · intro q
                                  exact Fin.elim0 q
                      · exact by
                          constructor
                          · exact by
                              intro h
                              exact False.elim ((by decide : ¬ (LexLE [] [2, 2, 1, 1, 2] ∧ LexLE [2, 2, 1, 1, 2] [2, 1, 1, 2, 2])) h)
                          · intro q
                            exact Fin.elim0 q
                · exact by
                    constructor
                    · exact by
                        intro h
                        exact False.elim ((by decide : ¬ (LexLE [] [2, 2, 1, 2] ∧ LexLE [2, 2, 1, 2] [2, 1, 2, 2])) h)
                    · intro q
                      fin_cases q
                      · exact by
                          constructor
                          · exact by
                              intro h
                              exact False.elim ((by decide : ¬ (LexLE [] [2, 2, 1, 2, 1] ∧ LexLE [2, 2, 1, 2, 1] [1, 2, 1, 2, 2])) h)
                          · intro q
                            exact Fin.elim0 q
                · exact by
                    constructor
                    · exact by
                        intro _
                        exact k16t8_cover1371
                    · intro q
                      exact Fin.elim0 q
          · exact by
              constructor
              · exact by
                  intro _
                  exact k16t8_cover1372
              · intro q
                fin_cases q
                · exact by
                    constructor
                    · exact by
                        intro h
                        exact False.elim ((by decide : ¬ (LexLE [] [2, 2, 2, 1] ∧ LexLE [2, 2, 2, 1] [1, 2, 2, 2])) h)
                    · intro q
                      fin_cases q
                      · exact by
                          constructor
                          · exact by
                              intro h
                              exact False.elim ((by decide : ¬ (LexLE [] [2, 2, 2, 1, 1] ∧ LexLE [2, 2, 2, 1, 1] [1, 1, 2, 2, 2])) h)
                          · intro q
                            exact Fin.elim0 q
                · exact by
                    constructor
                    · exact by
                        intro _
                        exact k16t8_cover1373
                    · intro q
                      exact Fin.elim0 q
          · exact by
              constructor
              · exact by
                  intro _
                  exact k16t8_cover1374
              · intro q
                fin_cases q
                · exact by
                    constructor
                    · exact by
                        intro h
                        exact False.elim ((by decide : ¬ (LexLE [] [2, 2, 3, 1] ∧ LexLE [2, 2, 3, 1] [1, 3, 2, 2])) h)
                    · intro q
                      exact Fin.elim0 q
          · exact by
              constructor
              · exact by
                  intro _
                  exact k16t8_cover1375
              · intro q
                exact Fin.elim0 q
    · exact by
        constructor
        · exact by
            intro _
            exact k16t8_cover1376
        · intro q
          fin_cases q
          · exact by
              constructor
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [] [2, 3, 1] ∧ LexLE [2, 3, 1] [1, 3, 2])) h)
              · intro q
                fin_cases q
                · exact by
                    constructor
                    · exact by
                        intro h
                        exact False.elim ((by decide : ¬ (LexLE [] [2, 3, 1, 1] ∧ LexLE [2, 3, 1, 1] [1, 1, 3, 2])) h)
                    · intro q
                      fin_cases q
                      · exact by
                          constructor
                          · exact by
                              intro h
                              exact False.elim ((by decide : ¬ (LexLE [] [2, 3, 1, 1, 1] ∧ LexLE [2, 3, 1, 1, 1] [1, 1, 1, 3, 2])) h)
                          · intro q
                            exact Fin.elim0 q
                · exact by
                    constructor
                    · exact by
                        intro h
                        exact False.elim ((by decide : ¬ (LexLE [] [2, 3, 1, 2] ∧ LexLE [2, 3, 1, 2] [2, 1, 3, 2])) h)
                    · intro q
                      exact Fin.elim0 q
          · exact by
              constructor
              · exact by
                  intro _
                  exact k16t8_cover1378
              · intro q
                fin_cases q
                · exact by
                    constructor
                    · exact by
                        intro h
                        exact False.elim ((by decide : ¬ (LexLE [] [2, 3, 2, 1] ∧ LexLE [2, 3, 2, 1] [1, 2, 3, 2])) h)
                    · intro q
                      exact Fin.elim0 q
          · exact by
              constructor
              · exact by
                  intro _
                  exact k16t8_cover1379
              · intro q
                exact Fin.elim0 q
    · exact by
        constructor
        · exact by
            intro _
            exact k16t8_cover1380
        · intro q
          fin_cases q
          · exact by
              constructor
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [] [2, 4, 1] ∧ LexLE [2, 4, 1] [1, 4, 2])) h)
              · intro q
                fin_cases q
                · exact by
                    constructor
                    · exact by
                        intro h
                        exact False.elim ((by decide : ¬ (LexLE [] [2, 4, 1, 1] ∧ LexLE [2, 4, 1, 1] [1, 1, 4, 2])) h)
                    · intro q
                      exact Fin.elim0 q
          · exact by
              constructor
              · exact by
                  intro _
                  exact k16t8_cover1381
              · intro q
                exact Fin.elim0 q
    · exact by
        constructor
        · exact by
            intro _
            exact k16t8_cover1382
        · intro q
          fin_cases q
          · exact by
              constructor
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [] [2, 5, 1] ∧ LexLE [2, 5, 1] [1, 5, 2])) h)
              · intro q
                exact Fin.elim0 q
    · exact by
        constructor
        · exact by
            intro _
            exact k16t8_cover1383
        · intro q
          exact Fin.elim0 q

private theorem k16t8_cover1387 : ∀ P ∈ pathPatterns 4 2 [3], HasCheckedCertificate 16 8 ([[3], [3]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [3] [] ∧ LexLE [] [])) h)
      · intro q
        fin_cases q
        · exact by
            constructor
            · exact by
                intro h
                exact False.elim ((by decide : ¬ (LexLE [3] [1] ∧ LexLE [1] [1])) h)
            · intro q
              fin_cases q
              · exact by
                  constructor
                  · exact by
                      intro h
                      exact False.elim ((by decide : ¬ (LexLE [3] [1, 1] ∧ LexLE [1, 1] [1, 1])) h)
                  · intro q
                    exact Fin.elim0 q
        · exact by
            constructor
            · exact by
                intro h
                exact False.elim ((by decide : ¬ (LexLE [3] [2] ∧ LexLE [2] [2])) h)
            · intro q
              exact Fin.elim0 q

private theorem k16t8_cover1388 : ∀ P ∈ pathPatterns 4 1 [4], HasCheckedCertificate 16 8 ([[3], [4]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [4] [] ∧ LexLE [] [])) h)
      · intro q
        fin_cases q
        · exact by
            constructor
            · exact by
                intro h
                exact False.elim ((by decide : ¬ (LexLE [4] [1] ∧ LexLE [1] [1])) h)
            · intro q
              exact Fin.elim0 q

private theorem k16t8_cover1389 : ∀ P ∈ pathPatterns 4 0 [5], HasCheckedCertificate 16 8 ([[3], [5]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [5] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k16t8_seq1386 : amountSequenceForall 5 5 (fun tail =>
    (LexLE [3] ([] ++ tail) ∧ LexLE ([] ++ tail) ([] ++ tail).reverse) →
    ∀ P ∈ pathPatterns (5 - ([] ++ tail).length) (5 - ([] ++ tail).sum) ([] ++ tail),
      HasCheckedCertificate 16 8 ([[3]] ++ (([] ++ tail) :: P))) :=
by
  constructor
  · exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [3] [] ∧ LexLE [] [])) h)
  · intro q
    fin_cases q
    · exact by
        constructor
        · exact by
            intro h
            exact False.elim ((by decide : ¬ (LexLE [3] [1] ∧ LexLE [1] [1])) h)
        · intro q
          fin_cases q
          · exact by
              constructor
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [3] [1, 1] ∧ LexLE [1, 1] [1, 1])) h)
              · intro q
                fin_cases q
                · exact by
                    constructor
                    · exact by
                        intro h
                        exact False.elim ((by decide : ¬ (LexLE [3] [1, 1, 1] ∧ LexLE [1, 1, 1] [1, 1, 1])) h)
                    · intro q
                      fin_cases q
                      · exact by
                          constructor
                          · exact by
                              intro h
                              exact False.elim ((by decide : ¬ (LexLE [3] [1, 1, 1, 1] ∧ LexLE [1, 1, 1, 1] [1, 1, 1, 1])) h)
                          · intro q
                            fin_cases q
                            · exact by
                                intro h
                                exact False.elim ((by decide : ¬ (LexLE [3] [1, 1, 1, 1, 1] ∧ LexLE [1, 1, 1, 1, 1] [1, 1, 1, 1, 1])) h)
                      · exact by
                          constructor
                          · exact by
                              intro h
                              exact False.elim ((by decide : ¬ (LexLE [3] [1, 1, 1, 2] ∧ LexLE [1, 1, 1, 2] [2, 1, 1, 1])) h)
                          · intro q
                            exact Fin.elim0 q
                · exact by
                    constructor
                    · exact by
                        intro h
                        exact False.elim ((by decide : ¬ (LexLE [3] [1, 1, 2] ∧ LexLE [1, 1, 2] [2, 1, 1])) h)
                    · intro q
                      fin_cases q
                      · exact by
                          constructor
                          · exact by
                              intro h
                              exact False.elim ((by decide : ¬ (LexLE [3] [1, 1, 2, 1] ∧ LexLE [1, 1, 2, 1] [1, 2, 1, 1])) h)
                          · intro q
                            exact Fin.elim0 q
                · exact by
                    constructor
                    · exact by
                        intro h
                        exact False.elim ((by decide : ¬ (LexLE [3] [1, 1, 3] ∧ LexLE [1, 1, 3] [3, 1, 1])) h)
                    · intro q
                      exact Fin.elim0 q
          · exact by
              constructor
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [3] [1, 2] ∧ LexLE [1, 2] [2, 1])) h)
              · intro q
                fin_cases q
                · exact by
                    constructor
                    · exact by
                        intro h
                        exact False.elim ((by decide : ¬ (LexLE [3] [1, 2, 1] ∧ LexLE [1, 2, 1] [1, 2, 1])) h)
                    · intro q
                      fin_cases q
                      · exact by
                          constructor
                          · exact by
                              intro h
                              exact False.elim ((by decide : ¬ (LexLE [3] [1, 2, 1, 1] ∧ LexLE [1, 2, 1, 1] [1, 1, 2, 1])) h)
                          · intro q
                            exact Fin.elim0 q
                · exact by
                    constructor
                    · exact by
                        intro h
                        exact False.elim ((by decide : ¬ (LexLE [3] [1, 2, 2] ∧ LexLE [1, 2, 2] [2, 2, 1])) h)
                    · intro q
                      exact Fin.elim0 q
          · exact by
              constructor
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [3] [1, 3] ∧ LexLE [1, 3] [3, 1])) h)
              · intro q
                fin_cases q
                · exact by
                    constructor
                    · exact by
                        intro h
                        exact False.elim ((by decide : ¬ (LexLE [3] [1, 3, 1] ∧ LexLE [1, 3, 1] [1, 3, 1])) h)
                    · intro q
                      exact Fin.elim0 q
          · exact by
              constructor
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [3] [1, 4] ∧ LexLE [1, 4] [4, 1])) h)
              · intro q
                exact Fin.elim0 q
    · exact by
        constructor
        · exact by
            intro h
            exact False.elim ((by decide : ¬ (LexLE [3] [2] ∧ LexLE [2] [2])) h)
        · intro q
          fin_cases q
          · exact by
              constructor
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [3] [2, 1] ∧ LexLE [2, 1] [1, 2])) h)
              · intro q
                fin_cases q
                · exact by
                    constructor
                    · exact by
                        intro h
                        exact False.elim ((by decide : ¬ (LexLE [3] [2, 1, 1] ∧ LexLE [2, 1, 1] [1, 1, 2])) h)
                    · intro q
                      fin_cases q
                      · exact by
                          constructor
                          · exact by
                              intro h
                              exact False.elim ((by decide : ¬ (LexLE [3] [2, 1, 1, 1] ∧ LexLE [2, 1, 1, 1] [1, 1, 1, 2])) h)
                          · intro q
                            exact Fin.elim0 q
                · exact by
                    constructor
                    · exact by
                        intro h
                        exact False.elim ((by decide : ¬ (LexLE [3] [2, 1, 2] ∧ LexLE [2, 1, 2] [2, 1, 2])) h)
                    · intro q
                      exact Fin.elim0 q
          · exact by
              constructor
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [3] [2, 2] ∧ LexLE [2, 2] [2, 2])) h)
              · intro q
                fin_cases q
                · exact by
                    constructor
                    · exact by
                        intro h
                        exact False.elim ((by decide : ¬ (LexLE [3] [2, 2, 1] ∧ LexLE [2, 2, 1] [1, 2, 2])) h)
                    · intro q
                      exact Fin.elim0 q
          · exact by
              constructor
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [3] [2, 3] ∧ LexLE [2, 3] [3, 2])) h)
              · intro q
                exact Fin.elim0 q
    · exact by
        constructor
        · exact by
            intro _
            exact k16t8_cover1387
        · intro q
          fin_cases q
          · exact by
              constructor
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [3] [3, 1] ∧ LexLE [3, 1] [1, 3])) h)
              · intro q
                fin_cases q
                · exact by
                    constructor
                    · exact by
                        intro h
                        exact False.elim ((by decide : ¬ (LexLE [3] [3, 1, 1] ∧ LexLE [3, 1, 1] [1, 1, 3])) h)
                    · intro q
                      exact Fin.elim0 q
          · exact by
              constructor
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [3] [3, 2] ∧ LexLE [3, 2] [2, 3])) h)
              · intro q
                exact Fin.elim0 q
    · exact by
        constructor
        · exact by
            intro _
            exact k16t8_cover1388
        · intro q
          fin_cases q
          · exact by
              constructor
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [3] [4, 1] ∧ LexLE [4, 1] [1, 4])) h)
              · intro q
                exact Fin.elim0 q
    · exact by
        constructor
        · exact by
            intro _
            exact k16t8_cover1389
        · intro q
          exact Fin.elim0 q

private theorem k16t8_cover1385 : ∀ P ∈ pathPatterns 6 5 [3], HasCheckedCertificate 16 8 ([[3]] ++ P) := by
  apply pathPatterns_forall_step
  exact k16t8_seq1386


private theorem k16t8_cover1390 : ∀ P ∈ pathPatterns 3 0 [3, 1, 1, 3], HasCheckedCertificate 16 8 ([[3, 1, 1, 3]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [3, 1, 1, 3] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k16t8_cover1391 : ∀ P ∈ pathPatterns 4 1 [3, 1, 3], HasCheckedCertificate 16 8 ([[3, 1, 3]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [3, 1, 3] [] ∧ LexLE [] [])) h)
      · intro q
        fin_cases q
        · exact by
            constructor
            · exact by
                intro h
                exact False.elim ((by decide : ¬ (LexLE [3, 1, 3] [1] ∧ LexLE [1] [1])) h)
            · intro q
              exact Fin.elim0 q

private theorem k16t8_cover1392 : ∀ P ∈ pathPatterns 4 0 [3, 1, 4], HasCheckedCertificate 16 8 ([[3, 1, 4]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [3, 1, 4] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k16t8_cover1393 : ∀ P ∈ pathPatterns 4 0 [3, 2, 3], HasCheckedCertificate 16 8 ([[3, 2, 3]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [3, 2, 3] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k16t8_cover1394 : ∀ P ∈ pathPatterns 5 2 [3, 3], HasCheckedCertificate 16 8 ([[3, 3]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [3, 3] [] ∧ LexLE [] [])) h)
      · intro q
        fin_cases q
        · exact by
            constructor
            · exact by
                intro h
                exact False.elim ((by decide : ¬ (LexLE [3, 3] [1] ∧ LexLE [1] [1])) h)
            · intro q
              fin_cases q
              · exact by
                  constructor
                  · exact by
                      intro h
                      exact False.elim ((by decide : ¬ (LexLE [3, 3] [1, 1] ∧ LexLE [1, 1] [1, 1])) h)
                  · intro q
                    exact Fin.elim0 q
        · exact by
            constructor
            · exact by
                intro h
                exact False.elim ((by decide : ¬ (LexLE [3, 3] [2] ∧ LexLE [2] [2])) h)
            · intro q
              exact Fin.elim0 q

private theorem k16t8_cover1395 : ∀ P ∈ pathPatterns 5 1 [3, 4], HasCheckedCertificate 16 8 ([[3, 4]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [3, 4] [] ∧ LexLE [] [])) h)
      · intro q
        fin_cases q
        · exact by
            constructor
            · exact by
                intro h
                exact False.elim ((by decide : ¬ (LexLE [3, 4] [1] ∧ LexLE [1] [1])) h)
            · intro q
              exact Fin.elim0 q

private theorem k16t8_cover1396 : ∀ P ∈ pathPatterns 5 0 [3, 5], HasCheckedCertificate 16 8 ([[3, 5]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [3, 5] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k16t8_seq1384 : amountSequenceForall 6 5 (fun tail =>
    (LexLE [] ([3] ++ tail) ∧ LexLE ([3] ++ tail) ([3] ++ tail).reverse) →
    ∀ P ∈ pathPatterns (7 - ([3] ++ tail).length) (8 - ([3] ++ tail).sum) ([3] ++ tail),
      HasCheckedCertificate 16 8 ([] ++ (([3] ++ tail) :: P))) :=
by
  constructor
  · exact by
      intro _
      exact k16t8_cover1385
  · intro q
    fin_cases q
    · exact by
        constructor
        · exact by
            intro h
            exact False.elim ((by decide : ¬ (LexLE [] [3, 1] ∧ LexLE [3, 1] [1, 3])) h)
        · intro q
          fin_cases q
          · exact by
              constructor
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [] [3, 1, 1] ∧ LexLE [3, 1, 1] [1, 1, 3])) h)
              · intro q
                fin_cases q
                · exact by
                    constructor
                    · exact by
                        intro h
                        exact False.elim ((by decide : ¬ (LexLE [] [3, 1, 1, 1] ∧ LexLE [3, 1, 1, 1] [1, 1, 1, 3])) h)
                    · intro q
                      fin_cases q
                      · exact by
                          constructor
                          · exact by
                              intro h
                              exact False.elim ((by decide : ¬ (LexLE [] [3, 1, 1, 1, 1] ∧ LexLE [3, 1, 1, 1, 1] [1, 1, 1, 1, 3])) h)
                          · intro q
                            fin_cases q
                            · exact by
                                constructor
                                · exact by
                                    intro h
                                    exact False.elim ((by decide : ¬ (LexLE [] [3, 1, 1, 1, 1, 1] ∧ LexLE [3, 1, 1, 1, 1, 1] [1, 1, 1, 1, 1, 3])) h)
                                · intro q
                                  exact Fin.elim0 q
                      · exact by
                          constructor
                          · exact by
                              intro h
                              exact False.elim ((by decide : ¬ (LexLE [] [3, 1, 1, 1, 2] ∧ LexLE [3, 1, 1, 1, 2] [2, 1, 1, 1, 3])) h)
                          · intro q
                            exact Fin.elim0 q
                · exact by
                    constructor
                    · exact by
                        intro h
                        exact False.elim ((by decide : ¬ (LexLE [] [3, 1, 1, 2] ∧ LexLE [3, 1, 1, 2] [2, 1, 1, 3])) h)
                    · intro q
                      fin_cases q
                      · exact by
                          constructor
                          · exact by
                              intro h
                              exact False.elim ((by decide : ¬ (LexLE [] [3, 1, 1, 2, 1] ∧ LexLE [3, 1, 1, 2, 1] [1, 2, 1, 1, 3])) h)
                          · intro q
                            exact Fin.elim0 q
                · exact by
                    constructor
                    · exact by
                        intro _
                        exact k16t8_cover1390
                    · intro q
                      exact Fin.elim0 q
          · exact by
              constructor
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [] [3, 1, 2] ∧ LexLE [3, 1, 2] [2, 1, 3])) h)
              · intro q
                fin_cases q
                · exact by
                    constructor
                    · exact by
                        intro h
                        exact False.elim ((by decide : ¬ (LexLE [] [3, 1, 2, 1] ∧ LexLE [3, 1, 2, 1] [1, 2, 1, 3])) h)
                    · intro q
                      fin_cases q
                      · exact by
                          constructor
                          · exact by
                              intro h
                              exact False.elim ((by decide : ¬ (LexLE [] [3, 1, 2, 1, 1] ∧ LexLE [3, 1, 2, 1, 1] [1, 1, 2, 1, 3])) h)
                          · intro q
                            exact Fin.elim0 q
                · exact by
                    constructor
                    · exact by
                        intro h
                        exact False.elim ((by decide : ¬ (LexLE [] [3, 1, 2, 2] ∧ LexLE [3, 1, 2, 2] [2, 2, 1, 3])) h)
                    · intro q
                      exact Fin.elim0 q
          · exact by
              constructor
              · exact by
                  intro _
                  exact k16t8_cover1391
              · intro q
                fin_cases q
                · exact by
                    constructor
                    · exact by
                        intro h
                        exact False.elim ((by decide : ¬ (LexLE [] [3, 1, 3, 1] ∧ LexLE [3, 1, 3, 1] [1, 3, 1, 3])) h)
                    · intro q
                      exact Fin.elim0 q
          · exact by
              constructor
              · exact by
                  intro _
                  exact k16t8_cover1392
              · intro q
                exact Fin.elim0 q
    · exact by
        constructor
        · exact by
            intro h
            exact False.elim ((by decide : ¬ (LexLE [] [3, 2] ∧ LexLE [3, 2] [2, 3])) h)
        · intro q
          fin_cases q
          · exact by
              constructor
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [] [3, 2, 1] ∧ LexLE [3, 2, 1] [1, 2, 3])) h)
              · intro q
                fin_cases q
                · exact by
                    constructor
                    · exact by
                        intro h
                        exact False.elim ((by decide : ¬ (LexLE [] [3, 2, 1, 1] ∧ LexLE [3, 2, 1, 1] [1, 1, 2, 3])) h)
                    · intro q
                      fin_cases q
                      · exact by
                          constructor
                          · exact by
                              intro h
                              exact False.elim ((by decide : ¬ (LexLE [] [3, 2, 1, 1, 1] ∧ LexLE [3, 2, 1, 1, 1] [1, 1, 1, 2, 3])) h)
                          · intro q
                            exact Fin.elim0 q
                · exact by
                    constructor
                    · exact by
                        intro h
                        exact False.elim ((by decide : ¬ (LexLE [] [3, 2, 1, 2] ∧ LexLE [3, 2, 1, 2] [2, 1, 2, 3])) h)
                    · intro q
                      exact Fin.elim0 q
          · exact by
              constructor
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [] [3, 2, 2] ∧ LexLE [3, 2, 2] [2, 2, 3])) h)
              · intro q
                fin_cases q
                · exact by
                    constructor
                    · exact by
                        intro h
                        exact False.elim ((by decide : ¬ (LexLE [] [3, 2, 2, 1] ∧ LexLE [3, 2, 2, 1] [1, 2, 2, 3])) h)
                    · intro q
                      exact Fin.elim0 q
          · exact by
              constructor
              · exact by
                  intro _
                  exact k16t8_cover1393
              · intro q
                exact Fin.elim0 q
    · exact by
        constructor
        · exact by
            intro _
            exact k16t8_cover1394
        · intro q
          fin_cases q
          · exact by
              constructor
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [] [3, 3, 1] ∧ LexLE [3, 3, 1] [1, 3, 3])) h)
              · intro q
                fin_cases q
                · exact by
                    constructor
                    · exact by
                        intro h
                        exact False.elim ((by decide : ¬ (LexLE [] [3, 3, 1, 1] ∧ LexLE [3, 3, 1, 1] [1, 1, 3, 3])) h)
                    · intro q
                      exact Fin.elim0 q
          · exact by
              constructor
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [] [3, 3, 2] ∧ LexLE [3, 3, 2] [2, 3, 3])) h)
              · intro q
                exact Fin.elim0 q
    · exact by
        constructor
        · exact by
            intro _
            exact k16t8_cover1395
        · intro q
          fin_cases q
          · exact by
              constructor
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [] [3, 4, 1] ∧ LexLE [3, 4, 1] [1, 4, 3])) h)
              · intro q
                exact Fin.elim0 q
    · exact by
        constructor
        · exact by
            intro _
            exact k16t8_cover1396
        · intro q
          exact Fin.elim0 q

private theorem k16t8_cover1398 : ∀ P ∈ pathPatterns 4 0 [4], HasCheckedCertificate 16 8 ([[4], [4]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [4] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k16t8_cover1397 : ∀ P ∈ pathPatterns 6 4 [4], HasCheckedCertificate 16 8 ([[4]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [4] [] ∧ LexLE [] [])) h)
      · intro q
        fin_cases q
        · exact by
            constructor
            · exact by
                intro h
                exact False.elim ((by decide : ¬ (LexLE [4] [1] ∧ LexLE [1] [1])) h)
            · intro q
              fin_cases q
              · exact by
                  constructor
                  · exact by
                      intro h
                      exact False.elim ((by decide : ¬ (LexLE [4] [1, 1] ∧ LexLE [1, 1] [1, 1])) h)
                  · intro q
                    fin_cases q
                    · exact by
                        constructor
                        · exact by
                            intro h
                            exact False.elim ((by decide : ¬ (LexLE [4] [1, 1, 1] ∧ LexLE [1, 1, 1] [1, 1, 1])) h)
                        · intro q
                          fin_cases q
                          · exact by
                              constructor
                              · exact by
                                  intro h
                                  exact False.elim ((by decide : ¬ (LexLE [4] [1, 1, 1, 1] ∧ LexLE [1, 1, 1, 1] [1, 1, 1, 1])) h)
                              · intro q
                                exact Fin.elim0 q
                    · exact by
                        constructor
                        · exact by
                            intro h
                            exact False.elim ((by decide : ¬ (LexLE [4] [1, 1, 2] ∧ LexLE [1, 1, 2] [2, 1, 1])) h)
                        · intro q
                          exact Fin.elim0 q
              · exact by
                  constructor
                  · exact by
                      intro h
                      exact False.elim ((by decide : ¬ (LexLE [4] [1, 2] ∧ LexLE [1, 2] [2, 1])) h)
                  · intro q
                    fin_cases q
                    · exact by
                        constructor
                        · exact by
                            intro h
                            exact False.elim ((by decide : ¬ (LexLE [4] [1, 2, 1] ∧ LexLE [1, 2, 1] [1, 2, 1])) h)
                        · intro q
                          exact Fin.elim0 q
              · exact by
                  constructor
                  · exact by
                      intro h
                      exact False.elim ((by decide : ¬ (LexLE [4] [1, 3] ∧ LexLE [1, 3] [3, 1])) h)
                  · intro q
                    exact Fin.elim0 q
        · exact by
            constructor
            · exact by
                intro h
                exact False.elim ((by decide : ¬ (LexLE [4] [2] ∧ LexLE [2] [2])) h)
            · intro q
              fin_cases q
              · exact by
                  constructor
                  · exact by
                      intro h
                      exact False.elim ((by decide : ¬ (LexLE [4] [2, 1] ∧ LexLE [2, 1] [1, 2])) h)
                  · intro q
                    fin_cases q
                    · exact by
                        constructor
                        · exact by
                            intro h
                            exact False.elim ((by decide : ¬ (LexLE [4] [2, 1, 1] ∧ LexLE [2, 1, 1] [1, 1, 2])) h)
                        · intro q
                          exact Fin.elim0 q
              · exact by
                  constructor
                  · exact by
                      intro h
                      exact False.elim ((by decide : ¬ (LexLE [4] [2, 2] ∧ LexLE [2, 2] [2, 2])) h)
                  · intro q
                    exact Fin.elim0 q
        · exact by
            constructor
            · exact by
                intro h
                exact False.elim ((by decide : ¬ (LexLE [4] [3] ∧ LexLE [3] [3])) h)
            · intro q
              fin_cases q
              · exact by
                  constructor
                  · exact by
                      intro h
                      exact False.elim ((by decide : ¬ (LexLE [4] [3, 1] ∧ LexLE [3, 1] [1, 3])) h)
                  · intro q
                    exact Fin.elim0 q
        · exact by
            constructor
            · exact by
                intro _
                exact k16t8_cover1398
            · intro q
              exact Fin.elim0 q

private theorem k16t8_cover1399 : ∀ P ∈ pathPatterns 5 0 [4, 4], HasCheckedCertificate 16 8 ([[4, 4]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [4, 4] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k16t8_cover1400 : ∀ P ∈ pathPatterns 6 3 [5], HasCheckedCertificate 16 8 ([[5]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [5] [] ∧ LexLE [] [])) h)
      · intro q
        fin_cases q
        · exact by
            constructor
            · exact by
                intro h
                exact False.elim ((by decide : ¬ (LexLE [5] [1] ∧ LexLE [1] [1])) h)
            · intro q
              fin_cases q
              · exact by
                  constructor
                  · exact by
                      intro h
                      exact False.elim ((by decide : ¬ (LexLE [5] [1, 1] ∧ LexLE [1, 1] [1, 1])) h)
                  · intro q
                    fin_cases q
                    · exact by
                        constructor
                        · exact by
                            intro h
                            exact False.elim ((by decide : ¬ (LexLE [5] [1, 1, 1] ∧ LexLE [1, 1, 1] [1, 1, 1])) h)
                        · intro q
                          exact Fin.elim0 q
              · exact by
                  constructor
                  · exact by
                      intro h
                      exact False.elim ((by decide : ¬ (LexLE [5] [1, 2] ∧ LexLE [1, 2] [2, 1])) h)
                  · intro q
                    exact Fin.elim0 q
        · exact by
            constructor
            · exact by
                intro h
                exact False.elim ((by decide : ¬ (LexLE [5] [2] ∧ LexLE [2] [2])) h)
            · intro q
              fin_cases q
              · exact by
                  constructor
                  · exact by
                      intro h
                      exact False.elim ((by decide : ¬ (LexLE [5] [2, 1] ∧ LexLE [2, 1] [1, 2])) h)
                  · intro q
                    exact Fin.elim0 q
        · exact by
            constructor
            · exact by
                intro h
                exact False.elim ((by decide : ¬ (LexLE [5] [3] ∧ LexLE [3] [3])) h)
            · intro q
              exact Fin.elim0 q

private theorem k16t8_cover1401 : ∀ P ∈ pathPatterns 6 2 [6], HasCheckedCertificate 16 8 ([[6]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [6] [] ∧ LexLE [] [])) h)
      · intro q
        fin_cases q
        · exact by
            constructor
            · exact by
                intro h
                exact False.elim ((by decide : ¬ (LexLE [6] [1] ∧ LexLE [1] [1])) h)
            · intro q
              fin_cases q
              · exact by
                  constructor
                  · exact by
                      intro h
                      exact False.elim ((by decide : ¬ (LexLE [6] [1, 1] ∧ LexLE [1, 1] [1, 1])) h)
                  · intro q
                    exact Fin.elim0 q
        · exact by
            constructor
            · exact by
                intro h
                exact False.elim ((by decide : ¬ (LexLE [6] [2] ∧ LexLE [2] [2])) h)
            · intro q
              exact Fin.elim0 q

private theorem k16t8_cover1402 : ∀ P ∈ pathPatterns 6 1 [7], HasCheckedCertificate 16 8 ([[7]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [7] [] ∧ LexLE [] [])) h)
      · intro q
        fin_cases q
        · exact by
            constructor
            · exact by
                intro h
                exact False.elim ((by decide : ¬ (LexLE [7] [1] ∧ LexLE [1] [1])) h)
            · intro q
              exact Fin.elim0 q

private theorem k16t8_cover1403 : ∀ P ∈ pathPatterns 6 0 [8], HasCheckedCertificate 16 8 ([[8]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [8] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k16t8_seq2 : amountSequenceForall 7 8 (fun tail =>
    (LexLE [] ([] ++ tail) ∧ LexLE ([] ++ tail) ([] ++ tail).reverse) →
    ∀ P ∈ pathPatterns (7 - ([] ++ tail).length) (8 - ([] ++ tail).sum) ([] ++ tail),
      HasCheckedCertificate 16 8 ([] ++ (([] ++ tail) :: P))) :=
by
  constructor
  · exact by
      intro _
      exact k16t8_cover3
  · intro q
    fin_cases q
    · exact k16t8_seq917

    · exact k16t8_seq1327

    · exact k16t8_seq1384

    · exact by
        constructor
        · exact by
            intro _
            exact k16t8_cover1397
        · intro q
          fin_cases q
          · exact by
              constructor
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [] [4, 1] ∧ LexLE [4, 1] [1, 4])) h)
              · intro q
                fin_cases q
                · exact by
                    constructor
                    · exact by
                        intro h
                        exact False.elim ((by decide : ¬ (LexLE [] [4, 1, 1] ∧ LexLE [4, 1, 1] [1, 1, 4])) h)
                    · intro q
                      fin_cases q
                      · exact by
                          constructor
                          · exact by
                              intro h
                              exact False.elim ((by decide : ¬ (LexLE [] [4, 1, 1, 1] ∧ LexLE [4, 1, 1, 1] [1, 1, 1, 4])) h)
                          · intro q
                            fin_cases q
                            · exact by
                                constructor
                                · exact by
                                    intro h
                                    exact False.elim ((by decide : ¬ (LexLE [] [4, 1, 1, 1, 1] ∧ LexLE [4, 1, 1, 1, 1] [1, 1, 1, 1, 4])) h)
                                · intro q
                                  exact Fin.elim0 q
                      · exact by
                          constructor
                          · exact by
                              intro h
                              exact False.elim ((by decide : ¬ (LexLE [] [4, 1, 1, 2] ∧ LexLE [4, 1, 1, 2] [2, 1, 1, 4])) h)
                          · intro q
                            exact Fin.elim0 q
                · exact by
                    constructor
                    · exact by
                        intro h
                        exact False.elim ((by decide : ¬ (LexLE [] [4, 1, 2] ∧ LexLE [4, 1, 2] [2, 1, 4])) h)
                    · intro q
                      fin_cases q
                      · exact by
                          constructor
                          · exact by
                              intro h
                              exact False.elim ((by decide : ¬ (LexLE [] [4, 1, 2, 1] ∧ LexLE [4, 1, 2, 1] [1, 2, 1, 4])) h)
                          · intro q
                            exact Fin.elim0 q
                · exact by
                    constructor
                    · exact by
                        intro h
                        exact False.elim ((by decide : ¬ (LexLE [] [4, 1, 3] ∧ LexLE [4, 1, 3] [3, 1, 4])) h)
                    · intro q
                      exact Fin.elim0 q
          · exact by
              constructor
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [] [4, 2] ∧ LexLE [4, 2] [2, 4])) h)
              · intro q
                fin_cases q
                · exact by
                    constructor
                    · exact by
                        intro h
                        exact False.elim ((by decide : ¬ (LexLE [] [4, 2, 1] ∧ LexLE [4, 2, 1] [1, 2, 4])) h)
                    · intro q
                      fin_cases q
                      · exact by
                          constructor
                          · exact by
                              intro h
                              exact False.elim ((by decide : ¬ (LexLE [] [4, 2, 1, 1] ∧ LexLE [4, 2, 1, 1] [1, 1, 2, 4])) h)
                          · intro q
                            exact Fin.elim0 q
                · exact by
                    constructor
                    · exact by
                        intro h
                        exact False.elim ((by decide : ¬ (LexLE [] [4, 2, 2] ∧ LexLE [4, 2, 2] [2, 2, 4])) h)
                    · intro q
                      exact Fin.elim0 q
          · exact by
              constructor
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [] [4, 3] ∧ LexLE [4, 3] [3, 4])) h)
              · intro q
                fin_cases q
                · exact by
                    constructor
                    · exact by
                        intro h
                        exact False.elim ((by decide : ¬ (LexLE [] [4, 3, 1] ∧ LexLE [4, 3, 1] [1, 3, 4])) h)
                    · intro q
                      exact Fin.elim0 q
          · exact by
              constructor
              · exact by
                  intro _
                  exact k16t8_cover1399
              · intro q
                exact Fin.elim0 q
    · exact by
        constructor
        · exact by
            intro _
            exact k16t8_cover1400
        · intro q
          fin_cases q
          · exact by
              constructor
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [] [5, 1] ∧ LexLE [5, 1] [1, 5])) h)
              · intro q
                fin_cases q
                · exact by
                    constructor
                    · exact by
                        intro h
                        exact False.elim ((by decide : ¬ (LexLE [] [5, 1, 1] ∧ LexLE [5, 1, 1] [1, 1, 5])) h)
                    · intro q
                      fin_cases q
                      · exact by
                          constructor
                          · exact by
                              intro h
                              exact False.elim ((by decide : ¬ (LexLE [] [5, 1, 1, 1] ∧ LexLE [5, 1, 1, 1] [1, 1, 1, 5])) h)
                          · intro q
                            exact Fin.elim0 q
                · exact by
                    constructor
                    · exact by
                        intro h
                        exact False.elim ((by decide : ¬ (LexLE [] [5, 1, 2] ∧ LexLE [5, 1, 2] [2, 1, 5])) h)
                    · intro q
                      exact Fin.elim0 q
          · exact by
              constructor
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [] [5, 2] ∧ LexLE [5, 2] [2, 5])) h)
              · intro q
                fin_cases q
                · exact by
                    constructor
                    · exact by
                        intro h
                        exact False.elim ((by decide : ¬ (LexLE [] [5, 2, 1] ∧ LexLE [5, 2, 1] [1, 2, 5])) h)
                    · intro q
                      exact Fin.elim0 q
          · exact by
              constructor
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [] [5, 3] ∧ LexLE [5, 3] [3, 5])) h)
              · intro q
                exact Fin.elim0 q
    · exact by
        constructor
        · exact by
            intro _
            exact k16t8_cover1401
        · intro q
          fin_cases q
          · exact by
              constructor
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [] [6, 1] ∧ LexLE [6, 1] [1, 6])) h)
              · intro q
                fin_cases q
                · exact by
                    constructor
                    · exact by
                        intro h
                        exact False.elim ((by decide : ¬ (LexLE [] [6, 1, 1] ∧ LexLE [6, 1, 1] [1, 1, 6])) h)
                    · intro q
                      exact Fin.elim0 q
          · exact by
              constructor
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [] [6, 2] ∧ LexLE [6, 2] [2, 6])) h)
              · intro q
                exact Fin.elim0 q
    · exact by
        constructor
        · exact by
            intro _
            exact k16t8_cover1402
        · intro q
          fin_cases q
          · exact by
              constructor
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [] [7, 1] ∧ LexLE [7, 1] [1, 7])) h)
              · intro q
                exact Fin.elim0 q
    · exact by
        constructor
        · exact by
            intro _
            exact k16t8_cover1403
        · intro q
          exact Fin.elim0 q

private theorem k16t8_cover1 : ∀ P ∈ pathPatterns 8 8 [], HasCheckedCertificate 16 8 ([] ++ P) := by
  apply pathPatterns_forall_step
  exact k16t8_seq2


theorem coverage_k16_t8 :
    ∀ P ∈ pathPatterns 8 8, HasCheckedCertificate 16 8 P :=
  k16t8_cover1

end CycleClique.Construction.CertifiedCoverage

end OAI
