import OAI.Combinatorics.Ramsey.CycleClique.Construction.CertificatesK14
import OAI.Combinatorics.Ramsey.CycleClique.Construction.CertificateCoverage

namespace OAI

namespace CycleClique.Construction.CertifiedCoverage

private theorem k14t7_cover13 : ∀ P ∈ pathPatterns 0 7 [], HasCheckedCertificate 14 7 ([[], [], [], [], [], [], []] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k14t7p0, Certificates.k14t7p0_check⟩

private theorem k14t7_cover12 : ∀ P ∈ pathPatterns 1 7 [], HasCheckedCertificate 14 7 ([[], [], [], [], [], []] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro _
      exact k14t7_cover13

private theorem k14t7_cover14 : ∀ P ∈ pathPatterns 0 6 [1], HasCheckedCertificate 14 7 ([[], [], [], [], [], [1]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k14t7p1, Certificates.k14t7p1_check⟩

private theorem k14t7_cover15 : ∀ P ∈ pathPatterns 0 5 [2], HasCheckedCertificate 14 7 ([[], [], [], [], [], [2]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k14t7p2, Certificates.k14t7p2_check⟩

private theorem k14t7_cover16 : ∀ P ∈ pathPatterns 0 4 [3], HasCheckedCertificate 14 7 ([[], [], [], [], [], [3]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k14t7p3, Certificates.k14t7p3_check⟩

private theorem k14t7_cover17 : ∀ P ∈ pathPatterns 0 3 [4], HasCheckedCertificate 14 7 ([[], [], [], [], [], [4]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k14t7p4, Certificates.k14t7p4_check⟩

private theorem k14t7_cover18 : ∀ P ∈ pathPatterns 0 2 [5], HasCheckedCertificate 14 7 ([[], [], [], [], [], [5]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k14t7p5, Certificates.k14t7p5_check⟩

private theorem k14t7_cover19 : ∀ P ∈ pathPatterns 0 1 [6], HasCheckedCertificate 14 7 ([[], [], [], [], [], [6]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k14t7p6, Certificates.k14t7p6_check⟩

private theorem k14t7_cover20 : ∀ P ∈ pathPatterns 0 0 [7], HasCheckedCertificate 14 7 ([[], [], [], [], [], [7]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k14t7p7, Certificates.k14t7p7_check⟩

private theorem k14t7_cover11 : ∀ P ∈ pathPatterns 2 7 [], HasCheckedCertificate 14 7 ([[], [], [], [], []] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro _
          exact k14t7_cover12
      · intro q
        fin_cases q
        · exact by
            intro _
            exact k14t7_cover14
        · exact by
            intro _
            exact k14t7_cover15
        · exact by
            intro _
            exact k14t7_cover16
        · exact by
            intro _
            exact k14t7_cover17
        · exact by
            intro _
            exact k14t7_cover18
        · exact by
            intro _
            exact k14t7_cover19
        · exact by
            intro _
            exact k14t7_cover20

private theorem k14t7_cover21 : ∀ P ∈ pathPatterns 1 6 [1], HasCheckedCertificate 14 7 ([[], [], [], [], [1]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [1] [] ∧ LexLE [] [])) h)

private theorem k14t7_cover22 : ∀ P ∈ pathPatterns 0 5 [1, 1], HasCheckedCertificate 14 7 ([[], [], [], [], [1, 1]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k14t7p8, Certificates.k14t7p8_check⟩

private theorem k14t7_cover23 : ∀ P ∈ pathPatterns 0 4 [1, 2], HasCheckedCertificate 14 7 ([[], [], [], [], [1, 2]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k14t7p9, Certificates.k14t7p9_check⟩

private theorem k14t7_cover24 : ∀ P ∈ pathPatterns 0 3 [1, 3], HasCheckedCertificate 14 7 ([[], [], [], [], [1, 3]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k14t7p10, Certificates.k14t7p10_check⟩

private theorem k14t7_cover25 : ∀ P ∈ pathPatterns 0 2 [1, 4], HasCheckedCertificate 14 7 ([[], [], [], [], [1, 4]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k14t7p11, Certificates.k14t7p11_check⟩

private theorem k14t7_cover26 : ∀ P ∈ pathPatterns 0 1 [1, 5], HasCheckedCertificate 14 7 ([[], [], [], [], [1, 5]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k14t7p12, Certificates.k14t7p12_check⟩

private theorem k14t7_cover27 : ∀ P ∈ pathPatterns 0 0 [1, 6], HasCheckedCertificate 14 7 ([[], [], [], [], [1, 6]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k14t7p13, Certificates.k14t7p13_check⟩

private theorem k14t7_cover28 : ∀ P ∈ pathPatterns 1 5 [2], HasCheckedCertificate 14 7 ([[], [], [], [], [2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [2] [] ∧ LexLE [] [])) h)

private theorem k14t7_cover29 : ∀ P ∈ pathPatterns 0 3 [2, 2], HasCheckedCertificate 14 7 ([[], [], [], [], [2, 2]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k14t7p14, Certificates.k14t7p14_check⟩

private theorem k14t7_cover30 : ∀ P ∈ pathPatterns 0 2 [2, 3], HasCheckedCertificate 14 7 ([[], [], [], [], [2, 3]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k14t7p15, Certificates.k14t7p15_check⟩

private theorem k14t7_cover31 : ∀ P ∈ pathPatterns 0 1 [2, 4], HasCheckedCertificate 14 7 ([[], [], [], [], [2, 4]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k14t7p16, Certificates.k14t7p16_check⟩

private theorem k14t7_cover32 : ∀ P ∈ pathPatterns 0 0 [2, 5], HasCheckedCertificate 14 7 ([[], [], [], [], [2, 5]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k14t7p17, Certificates.k14t7p17_check⟩

private theorem k14t7_cover33 : ∀ P ∈ pathPatterns 1 4 [3], HasCheckedCertificate 14 7 ([[], [], [], [], [3]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [3] [] ∧ LexLE [] [])) h)

private theorem k14t7_cover34 : ∀ P ∈ pathPatterns 0 1 [3, 3], HasCheckedCertificate 14 7 ([[], [], [], [], [3, 3]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k14t7p18, Certificates.k14t7p18_check⟩

private theorem k14t7_cover35 : ∀ P ∈ pathPatterns 0 0 [3, 4], HasCheckedCertificate 14 7 ([[], [], [], [], [3, 4]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k14t7p19, Certificates.k14t7p19_check⟩

private theorem k14t7_cover36 : ∀ P ∈ pathPatterns 1 3 [4], HasCheckedCertificate 14 7 ([[], [], [], [], [4]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [4] [] ∧ LexLE [] [])) h)

private theorem k14t7_cover37 : ∀ P ∈ pathPatterns 1 2 [5], HasCheckedCertificate 14 7 ([[], [], [], [], [5]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [5] [] ∧ LexLE [] [])) h)

private theorem k14t7_cover38 : ∀ P ∈ pathPatterns 1 1 [6], HasCheckedCertificate 14 7 ([[], [], [], [], [6]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [6] [] ∧ LexLE [] [])) h)

private theorem k14t7_cover39 : ∀ P ∈ pathPatterns 1 0 [7], HasCheckedCertificate 14 7 ([[], [], [], [], [7]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [7] [] ∧ LexLE [] [])) h)

private theorem k14t7_seq10 : amountSequenceForall 2 7 (fun tail =>
    (LexLE [] ([] ++ tail) ∧ LexLE ([] ++ tail) ([] ++ tail).reverse) →
    ∀ P ∈ pathPatterns (2 - ([] ++ tail).length) (7 - ([] ++ tail).sum) ([] ++ tail),
      HasCheckedCertificate 14 7 ([[], [], [], []] ++ (([] ++ tail) :: P))) :=
by
  constructor
  · exact by
      intro _
      exact k14t7_cover11
  · intro q
    fin_cases q
    · exact by
        constructor
        · exact by
            intro _
            exact k14t7_cover21
        · intro q
          fin_cases q
          · exact by
              intro _
              exact k14t7_cover22
          · exact by
              intro _
              exact k14t7_cover23
          · exact by
              intro _
              exact k14t7_cover24
          · exact by
              intro _
              exact k14t7_cover25
          · exact by
              intro _
              exact k14t7_cover26
          · exact by
              intro _
              exact k14t7_cover27
    · exact by
        constructor
        · exact by
            intro _
            exact k14t7_cover28
        · intro q
          fin_cases q
          · exact by
              intro h
              exact False.elim ((by decide : ¬ (LexLE [] [2, 1] ∧ LexLE [2, 1] [1, 2])) h)
          · exact by
              intro _
              exact k14t7_cover29
          · exact by
              intro _
              exact k14t7_cover30
          · exact by
              intro _
              exact k14t7_cover31
          · exact by
              intro _
              exact k14t7_cover32
    · exact by
        constructor
        · exact by
            intro _
            exact k14t7_cover33
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
              exact k14t7_cover34
          · exact by
              intro _
              exact k14t7_cover35
    · exact by
        constructor
        · exact by
            intro _
            exact k14t7_cover36
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
        constructor
        · exact by
            intro _
            exact k14t7_cover37
        · intro q
          fin_cases q
          · exact by
              intro h
              exact False.elim ((by decide : ¬ (LexLE [] [5, 1] ∧ LexLE [5, 1] [1, 5])) h)
          · exact by
              intro h
              exact False.elim ((by decide : ¬ (LexLE [] [5, 2] ∧ LexLE [5, 2] [2, 5])) h)
    · exact by
        constructor
        · exact by
            intro _
            exact k14t7_cover38
        · intro q
          fin_cases q
          · exact by
              intro h
              exact False.elim ((by decide : ¬ (LexLE [] [6, 1] ∧ LexLE [6, 1] [1, 6])) h)
    · exact by
        constructor
        · exact by
            intro _
            exact k14t7_cover39
        · intro q
          exact Fin.elim0 q

private theorem k14t7_cover9 : ∀ P ∈ pathPatterns 3 7 [], HasCheckedCertificate 14 7 ([[], [], [], []] ++ P) := by
  apply pathPatterns_forall_step
  exact k14t7_seq10


private theorem k14t7_cover41 : ∀ P ∈ pathPatterns 0 5 [1], HasCheckedCertificate 14 7 ([[], [], [], [1], [1]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k14t7p20, Certificates.k14t7p20_check⟩

private theorem k14t7_cover42 : ∀ P ∈ pathPatterns 0 4 [2], HasCheckedCertificate 14 7 ([[], [], [], [1], [2]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k14t7p21, Certificates.k14t7p21_check⟩

private theorem k14t7_cover43 : ∀ P ∈ pathPatterns 0 3 [3], HasCheckedCertificate 14 7 ([[], [], [], [1], [3]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k14t7p22, Certificates.k14t7p22_check⟩

private theorem k14t7_cover44 : ∀ P ∈ pathPatterns 0 2 [4], HasCheckedCertificate 14 7 ([[], [], [], [1], [4]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k14t7p23, Certificates.k14t7p23_check⟩

private theorem k14t7_cover45 : ∀ P ∈ pathPatterns 0 1 [5], HasCheckedCertificate 14 7 ([[], [], [], [1], [5]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k14t7p24, Certificates.k14t7p24_check⟩

private theorem k14t7_cover46 : ∀ P ∈ pathPatterns 0 0 [6], HasCheckedCertificate 14 7 ([[], [], [], [1], [6]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k14t7p25, Certificates.k14t7p25_check⟩

private theorem k14t7_cover40 : ∀ P ∈ pathPatterns 2 6 [1], HasCheckedCertificate 14 7 ([[], [], [], [1]] ++ P) := by
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
            exact k14t7_cover41
        · exact by
            intro _
            exact k14t7_cover42
        · exact by
            intro _
            exact k14t7_cover43
        · exact by
            intro _
            exact k14t7_cover44
        · exact by
            intro _
            exact k14t7_cover45
        · exact by
            intro _
            exact k14t7_cover46

private theorem k14t7_cover47 : ∀ P ∈ pathPatterns 1 5 [1, 1], HasCheckedCertificate 14 7 ([[], [], [], [1, 1]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [1, 1] [] ∧ LexLE [] [])) h)

private theorem k14t7_cover48 : ∀ P ∈ pathPatterns 0 4 [1, 1, 1], HasCheckedCertificate 14 7 ([[], [], [], [1, 1, 1]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k14t7p26, Certificates.k14t7p26_check⟩

private theorem k14t7_cover49 : ∀ P ∈ pathPatterns 0 3 [1, 1, 2], HasCheckedCertificate 14 7 ([[], [], [], [1, 1, 2]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k14t7p27, Certificates.k14t7p27_check⟩

private theorem k14t7_cover50 : ∀ P ∈ pathPatterns 0 2 [1, 1, 3], HasCheckedCertificate 14 7 ([[], [], [], [1, 1, 3]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k14t7p28, Certificates.k14t7p28_check⟩

private theorem k14t7_cover51 : ∀ P ∈ pathPatterns 0 1 [1, 1, 4], HasCheckedCertificate 14 7 ([[], [], [], [1, 1, 4]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k14t7p29, Certificates.k14t7p29_check⟩

private theorem k14t7_cover52 : ∀ P ∈ pathPatterns 0 0 [1, 1, 5], HasCheckedCertificate 14 7 ([[], [], [], [1, 1, 5]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k14t7p30, Certificates.k14t7p30_check⟩

private theorem k14t7_cover53 : ∀ P ∈ pathPatterns 1 4 [1, 2], HasCheckedCertificate 14 7 ([[], [], [], [1, 2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [1, 2] [] ∧ LexLE [] [])) h)

private theorem k14t7_cover54 : ∀ P ∈ pathPatterns 0 3 [1, 2, 1], HasCheckedCertificate 14 7 ([[], [], [], [1, 2, 1]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k14t7p31, Certificates.k14t7p31_check⟩

private theorem k14t7_cover55 : ∀ P ∈ pathPatterns 0 2 [1, 2, 2], HasCheckedCertificate 14 7 ([[], [], [], [1, 2, 2]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k14t7p32, Certificates.k14t7p32_check⟩

private theorem k14t7_cover56 : ∀ P ∈ pathPatterns 0 1 [1, 2, 3], HasCheckedCertificate 14 7 ([[], [], [], [1, 2, 3]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k14t7p33, Certificates.k14t7p33_check⟩

private theorem k14t7_cover57 : ∀ P ∈ pathPatterns 0 0 [1, 2, 4], HasCheckedCertificate 14 7 ([[], [], [], [1, 2, 4]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k14t7p34, Certificates.k14t7p34_check⟩

private theorem k14t7_cover58 : ∀ P ∈ pathPatterns 1 3 [1, 3], HasCheckedCertificate 14 7 ([[], [], [], [1, 3]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [1, 3] [] ∧ LexLE [] [])) h)

private theorem k14t7_cover59 : ∀ P ∈ pathPatterns 0 2 [1, 3, 1], HasCheckedCertificate 14 7 ([[], [], [], [1, 3, 1]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k14t7p35, Certificates.k14t7p35_check⟩

private theorem k14t7_cover60 : ∀ P ∈ pathPatterns 0 1 [1, 3, 2], HasCheckedCertificate 14 7 ([[], [], [], [1, 3, 2]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k14t7p36, Certificates.k14t7p36_check⟩

private theorem k14t7_cover61 : ∀ P ∈ pathPatterns 0 0 [1, 3, 3], HasCheckedCertificate 14 7 ([[], [], [], [1, 3, 3]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k14t7p37, Certificates.k14t7p37_check⟩

private theorem k14t7_cover62 : ∀ P ∈ pathPatterns 1 2 [1, 4], HasCheckedCertificate 14 7 ([[], [], [], [1, 4]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [1, 4] [] ∧ LexLE [] [])) h)

private theorem k14t7_cover63 : ∀ P ∈ pathPatterns 0 1 [1, 4, 1], HasCheckedCertificate 14 7 ([[], [], [], [1, 4, 1]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k14t7p38, Certificates.k14t7p38_check⟩

private theorem k14t7_cover64 : ∀ P ∈ pathPatterns 0 0 [1, 4, 2], HasCheckedCertificate 14 7 ([[], [], [], [1, 4, 2]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k14t7p39, Certificates.k14t7p39_check⟩

private theorem k14t7_cover65 : ∀ P ∈ pathPatterns 1 1 [1, 5], HasCheckedCertificate 14 7 ([[], [], [], [1, 5]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [1, 5] [] ∧ LexLE [] [])) h)

private theorem k14t7_cover66 : ∀ P ∈ pathPatterns 0 0 [1, 5, 1], HasCheckedCertificate 14 7 ([[], [], [], [1, 5, 1]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k14t7p40, Certificates.k14t7p40_check⟩

private theorem k14t7_cover67 : ∀ P ∈ pathPatterns 1 0 [1, 6], HasCheckedCertificate 14 7 ([[], [], [], [1, 6]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [1, 6] [] ∧ LexLE [] [])) h)

private theorem k14t7_cover69 : ∀ P ∈ pathPatterns 0 3 [2], HasCheckedCertificate 14 7 ([[], [], [], [2], [2]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k14t7p41, Certificates.k14t7p41_check⟩

private theorem k14t7_cover70 : ∀ P ∈ pathPatterns 0 2 [3], HasCheckedCertificate 14 7 ([[], [], [], [2], [3]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k14t7p42, Certificates.k14t7p42_check⟩

private theorem k14t7_cover71 : ∀ P ∈ pathPatterns 0 1 [4], HasCheckedCertificate 14 7 ([[], [], [], [2], [4]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k14t7p43, Certificates.k14t7p43_check⟩

private theorem k14t7_cover72 : ∀ P ∈ pathPatterns 0 0 [5], HasCheckedCertificate 14 7 ([[], [], [], [2], [5]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k14t7p44, Certificates.k14t7p44_check⟩

private theorem k14t7_cover68 : ∀ P ∈ pathPatterns 2 5 [2], HasCheckedCertificate 14 7 ([[], [], [], [2]] ++ P) := by
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
            exact k14t7_cover69
        · exact by
            intro _
            exact k14t7_cover70
        · exact by
            intro _
            exact k14t7_cover71
        · exact by
            intro _
            exact k14t7_cover72

private theorem k14t7_cover73 : ∀ P ∈ pathPatterns 0 2 [2, 1, 2], HasCheckedCertificate 14 7 ([[], [], [], [2, 1, 2]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k14t7p45, Certificates.k14t7p45_check⟩

private theorem k14t7_cover74 : ∀ P ∈ pathPatterns 0 1 [2, 1, 3], HasCheckedCertificate 14 7 ([[], [], [], [2, 1, 3]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k14t7p46, Certificates.k14t7p46_check⟩

private theorem k14t7_cover75 : ∀ P ∈ pathPatterns 0 0 [2, 1, 4], HasCheckedCertificate 14 7 ([[], [], [], [2, 1, 4]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k14t7p47, Certificates.k14t7p47_check⟩

private theorem k14t7_cover76 : ∀ P ∈ pathPatterns 1 3 [2, 2], HasCheckedCertificate 14 7 ([[], [], [], [2, 2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [2, 2] [] ∧ LexLE [] [])) h)

private theorem k14t7_cover77 : ∀ P ∈ pathPatterns 0 1 [2, 2, 2], HasCheckedCertificate 14 7 ([[], [], [], [2, 2, 2]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k14t7p48, Certificates.k14t7p48_check⟩

private theorem k14t7_cover78 : ∀ P ∈ pathPatterns 0 0 [2, 2, 3], HasCheckedCertificate 14 7 ([[], [], [], [2, 2, 3]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k14t7p49, Certificates.k14t7p49_check⟩

private theorem k14t7_cover79 : ∀ P ∈ pathPatterns 1 2 [2, 3], HasCheckedCertificate 14 7 ([[], [], [], [2, 3]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [2, 3] [] ∧ LexLE [] [])) h)

private theorem k14t7_cover80 : ∀ P ∈ pathPatterns 0 0 [2, 3, 2], HasCheckedCertificate 14 7 ([[], [], [], [2, 3, 2]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k14t7p50, Certificates.k14t7p50_check⟩

private theorem k14t7_cover81 : ∀ P ∈ pathPatterns 1 1 [2, 4], HasCheckedCertificate 14 7 ([[], [], [], [2, 4]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [2, 4] [] ∧ LexLE [] [])) h)

private theorem k14t7_cover82 : ∀ P ∈ pathPatterns 1 0 [2, 5], HasCheckedCertificate 14 7 ([[], [], [], [2, 5]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [2, 5] [] ∧ LexLE [] [])) h)

private theorem k14t7_cover84 : ∀ P ∈ pathPatterns 0 1 [3], HasCheckedCertificate 14 7 ([[], [], [], [3], [3]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k14t7p51, Certificates.k14t7p51_check⟩

private theorem k14t7_cover85 : ∀ P ∈ pathPatterns 0 0 [4], HasCheckedCertificate 14 7 ([[], [], [], [3], [4]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k14t7p52, Certificates.k14t7p52_check⟩

private theorem k14t7_cover83 : ∀ P ∈ pathPatterns 2 4 [3], HasCheckedCertificate 14 7 ([[], [], [], [3]] ++ P) := by
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
            exact k14t7_cover84
        · exact by
            intro _
            exact k14t7_cover85

private theorem k14t7_cover86 : ∀ P ∈ pathPatterns 0 0 [3, 1, 3], HasCheckedCertificate 14 7 ([[], [], [], [3, 1, 3]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k14t7p53, Certificates.k14t7p53_check⟩

private theorem k14t7_cover87 : ∀ P ∈ pathPatterns 1 1 [3, 3], HasCheckedCertificate 14 7 ([[], [], [], [3, 3]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [3, 3] [] ∧ LexLE [] [])) h)

private theorem k14t7_cover88 : ∀ P ∈ pathPatterns 1 0 [3, 4], HasCheckedCertificate 14 7 ([[], [], [], [3, 4]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [3, 4] [] ∧ LexLE [] [])) h)

private theorem k14t7_cover89 : ∀ P ∈ pathPatterns 2 3 [4], HasCheckedCertificate 14 7 ([[], [], [], [4]] ++ P) := by
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

private theorem k14t7_cover90 : ∀ P ∈ pathPatterns 2 2 [5], HasCheckedCertificate 14 7 ([[], [], [], [5]] ++ P) := by
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

private theorem k14t7_cover91 : ∀ P ∈ pathPatterns 2 1 [6], HasCheckedCertificate 14 7 ([[], [], [], [6]] ++ P) := by
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

private theorem k14t7_cover92 : ∀ P ∈ pathPatterns 2 0 [7], HasCheckedCertificate 14 7 ([[], [], [], [7]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [7] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k14t7_seq8 : amountSequenceForall 3 7 (fun tail =>
    (LexLE [] ([] ++ tail) ∧ LexLE ([] ++ tail) ([] ++ tail).reverse) →
    ∀ P ∈ pathPatterns (3 - ([] ++ tail).length) (7 - ([] ++ tail).sum) ([] ++ tail),
      HasCheckedCertificate 14 7 ([[], [], []] ++ (([] ++ tail) :: P))) :=
by
  constructor
  · exact by
      intro _
      exact k14t7_cover9
  · intro q
    fin_cases q
    · exact by
        constructor
        · exact by
            intro _
            exact k14t7_cover40
        · intro q
          fin_cases q
          · exact by
              constructor
              · exact by
                  intro _
                  exact k14t7_cover47
              · intro q
                fin_cases q
                · exact by
                    intro _
                    exact k14t7_cover48
                · exact by
                    intro _
                    exact k14t7_cover49
                · exact by
                    intro _
                    exact k14t7_cover50
                · exact by
                    intro _
                    exact k14t7_cover51
                · exact by
                    intro _
                    exact k14t7_cover52
          · exact by
              constructor
              · exact by
                  intro _
                  exact k14t7_cover53
              · intro q
                fin_cases q
                · exact by
                    intro _
                    exact k14t7_cover54
                · exact by
                    intro _
                    exact k14t7_cover55
                · exact by
                    intro _
                    exact k14t7_cover56
                · exact by
                    intro _
                    exact k14t7_cover57
          · exact by
              constructor
              · exact by
                  intro _
                  exact k14t7_cover58
              · intro q
                fin_cases q
                · exact by
                    intro _
                    exact k14t7_cover59
                · exact by
                    intro _
                    exact k14t7_cover60
                · exact by
                    intro _
                    exact k14t7_cover61
          · exact by
              constructor
              · exact by
                  intro _
                  exact k14t7_cover62
              · intro q
                fin_cases q
                · exact by
                    intro _
                    exact k14t7_cover63
                · exact by
                    intro _
                    exact k14t7_cover64
          · exact by
              constructor
              · exact by
                  intro _
                  exact k14t7_cover65
              · intro q
                fin_cases q
                · exact by
                    intro _
                    exact k14t7_cover66
          · exact by
              constructor
              · exact by
                  intro _
                  exact k14t7_cover67
              · intro q
                exact Fin.elim0 q
    · exact by
        constructor
        · exact by
            intro _
            exact k14t7_cover68
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
                    exact k14t7_cover73
                · exact by
                    intro _
                    exact k14t7_cover74
                · exact by
                    intro _
                    exact k14t7_cover75
          · exact by
              constructor
              · exact by
                  intro _
                  exact k14t7_cover76
              · intro q
                fin_cases q
                · exact by
                    intro h
                    exact False.elim ((by decide : ¬ (LexLE [] [2, 2, 1] ∧ LexLE [2, 2, 1] [1, 2, 2])) h)
                · exact by
                    intro _
                    exact k14t7_cover77
                · exact by
                    intro _
                    exact k14t7_cover78
          · exact by
              constructor
              · exact by
                  intro _
                  exact k14t7_cover79
              · intro q
                fin_cases q
                · exact by
                    intro h
                    exact False.elim ((by decide : ¬ (LexLE [] [2, 3, 1] ∧ LexLE [2, 3, 1] [1, 3, 2])) h)
                · exact by
                    intro _
                    exact k14t7_cover80
          · exact by
              constructor
              · exact by
                  intro _
                  exact k14t7_cover81
              · intro q
                fin_cases q
                · exact by
                    intro h
                    exact False.elim ((by decide : ¬ (LexLE [] [2, 4, 1] ∧ LexLE [2, 4, 1] [1, 4, 2])) h)
          · exact by
              constructor
              · exact by
                  intro _
                  exact k14t7_cover82
              · intro q
                exact Fin.elim0 q
    · exact by
        constructor
        · exact by
            intro _
            exact k14t7_cover83
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
                    exact k14t7_cover86
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
              constructor
              · exact by
                  intro _
                  exact k14t7_cover87
              · intro q
                fin_cases q
                · exact by
                    intro h
                    exact False.elim ((by decide : ¬ (LexLE [] [3, 3, 1] ∧ LexLE [3, 3, 1] [1, 3, 3])) h)
          · exact by
              constructor
              · exact by
                  intro _
                  exact k14t7_cover88
              · intro q
                exact Fin.elim0 q
    · exact by
        constructor
        · exact by
            intro _
            exact k14t7_cover89
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
              constructor
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [] [4, 3] ∧ LexLE [4, 3] [3, 4])) h)
              · intro q
                exact Fin.elim0 q
    · exact by
        constructor
        · exact by
            intro _
            exact k14t7_cover90
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
              constructor
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [] [5, 2] ∧ LexLE [5, 2] [2, 5])) h)
              · intro q
                exact Fin.elim0 q
    · exact by
        constructor
        · exact by
            intro _
            exact k14t7_cover91
        · intro q
          fin_cases q
          · exact by
              constructor
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [] [6, 1] ∧ LexLE [6, 1] [1, 6])) h)
              · intro q
                exact Fin.elim0 q
    · exact by
        constructor
        · exact by
            intro _
            exact k14t7_cover92
        · intro q
          exact Fin.elim0 q

private theorem k14t7_cover7 : ∀ P ∈ pathPatterns 4 7 [], HasCheckedCertificate 14 7 ([[], [], []] ++ P) := by
  apply pathPatterns_forall_step
  exact k14t7_seq8


private theorem k14t7_cover95 : ∀ P ∈ pathPatterns 1 5 [1], HasCheckedCertificate 14 7 ([[], [], [1], [1]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [1] [] ∧ LexLE [] [])) h)

private theorem k14t7_cover96 : ∀ P ∈ pathPatterns 0 4 [1, 1], HasCheckedCertificate 14 7 ([[], [], [1], [1, 1]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k14t7p54, Certificates.k14t7p54_check⟩

private theorem k14t7_cover97 : ∀ P ∈ pathPatterns 0 3 [1, 2], HasCheckedCertificate 14 7 ([[], [], [1], [1, 2]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k14t7p55, Certificates.k14t7p55_check⟩

private theorem k14t7_cover98 : ∀ P ∈ pathPatterns 0 2 [1, 3], HasCheckedCertificate 14 7 ([[], [], [1], [1, 3]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k14t7p56, Certificates.k14t7p56_check⟩

private theorem k14t7_cover99 : ∀ P ∈ pathPatterns 0 1 [1, 4], HasCheckedCertificate 14 7 ([[], [], [1], [1, 4]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k14t7p57, Certificates.k14t7p57_check⟩

private theorem k14t7_cover100 : ∀ P ∈ pathPatterns 0 0 [1, 5], HasCheckedCertificate 14 7 ([[], [], [1], [1, 5]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k14t7p58, Certificates.k14t7p58_check⟩

private theorem k14t7_cover101 : ∀ P ∈ pathPatterns 1 4 [2], HasCheckedCertificate 14 7 ([[], [], [1], [2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [2] [] ∧ LexLE [] [])) h)

private theorem k14t7_cover102 : ∀ P ∈ pathPatterns 0 2 [2, 2], HasCheckedCertificate 14 7 ([[], [], [1], [2, 2]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k14t7p59, Certificates.k14t7p59_check⟩

private theorem k14t7_cover103 : ∀ P ∈ pathPatterns 0 1 [2, 3], HasCheckedCertificate 14 7 ([[], [], [1], [2, 3]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k14t7p60, Certificates.k14t7p60_check⟩

private theorem k14t7_cover104 : ∀ P ∈ pathPatterns 0 0 [2, 4], HasCheckedCertificate 14 7 ([[], [], [1], [2, 4]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k14t7p61, Certificates.k14t7p61_check⟩

private theorem k14t7_cover105 : ∀ P ∈ pathPatterns 1 3 [3], HasCheckedCertificate 14 7 ([[], [], [1], [3]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [3] [] ∧ LexLE [] [])) h)

private theorem k14t7_cover106 : ∀ P ∈ pathPatterns 0 0 [3, 3], HasCheckedCertificate 14 7 ([[], [], [1], [3, 3]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k14t7p62, Certificates.k14t7p62_check⟩

private theorem k14t7_cover107 : ∀ P ∈ pathPatterns 1 2 [4], HasCheckedCertificate 14 7 ([[], [], [1], [4]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [4] [] ∧ LexLE [] [])) h)

private theorem k14t7_cover108 : ∀ P ∈ pathPatterns 1 1 [5], HasCheckedCertificate 14 7 ([[], [], [1], [5]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [5] [] ∧ LexLE [] [])) h)

private theorem k14t7_cover109 : ∀ P ∈ pathPatterns 1 0 [6], HasCheckedCertificate 14 7 ([[], [], [1], [6]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [6] [] ∧ LexLE [] [])) h)

private theorem k14t7_cover94 : ∀ P ∈ pathPatterns 3 6 [1], HasCheckedCertificate 14 7 ([[], [], [1]] ++ P) := by
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
                exact k14t7_cover95
            · intro q
              fin_cases q
              · exact by
                  intro _
                  exact k14t7_cover96
              · exact by
                  intro _
                  exact k14t7_cover97
              · exact by
                  intro _
                  exact k14t7_cover98
              · exact by
                  intro _
                  exact k14t7_cover99
              · exact by
                  intro _
                  exact k14t7_cover100
        · exact by
            constructor
            · exact by
                intro _
                exact k14t7_cover101
            · intro q
              fin_cases q
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [1] [2, 1] ∧ LexLE [2, 1] [1, 2])) h)
              · exact by
                  intro _
                  exact k14t7_cover102
              · exact by
                  intro _
                  exact k14t7_cover103
              · exact by
                  intro _
                  exact k14t7_cover104
        · exact by
            constructor
            · exact by
                intro _
                exact k14t7_cover105
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
                  exact k14t7_cover106
        · exact by
            constructor
            · exact by
                intro _
                exact k14t7_cover107
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
                exact k14t7_cover108
            · intro q
              fin_cases q
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [1] [5, 1] ∧ LexLE [5, 1] [1, 5])) h)
        · exact by
            constructor
            · exact by
                intro _
                exact k14t7_cover109
            · intro q
              exact Fin.elim0 q

private theorem k14t7_cover111 : ∀ P ∈ pathPatterns 0 3 [2], HasCheckedCertificate 14 7 ([[], [], [1, 1], [2]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k14t7p63, Certificates.k14t7p63_check⟩

private theorem k14t7_cover112 : ∀ P ∈ pathPatterns 0 2 [3], HasCheckedCertificate 14 7 ([[], [], [1, 1], [3]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k14t7p64, Certificates.k14t7p64_check⟩

private theorem k14t7_cover113 : ∀ P ∈ pathPatterns 0 1 [4], HasCheckedCertificate 14 7 ([[], [], [1, 1], [4]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k14t7p65, Certificates.k14t7p65_check⟩

private theorem k14t7_cover114 : ∀ P ∈ pathPatterns 0 0 [5], HasCheckedCertificate 14 7 ([[], [], [1, 1], [5]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k14t7p66, Certificates.k14t7p66_check⟩

private theorem k14t7_cover110 : ∀ P ∈ pathPatterns 2 5 [1, 1], HasCheckedCertificate 14 7 ([[], [], [1, 1]] ++ P) := by
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
            exact k14t7_cover111
        · exact by
            intro _
            exact k14t7_cover112
        · exact by
            intro _
            exact k14t7_cover113
        · exact by
            intro _
            exact k14t7_cover114

private theorem k14t7_cover115 : ∀ P ∈ pathPatterns 1 4 [1, 1, 1], HasCheckedCertificate 14 7 ([[], [], [1, 1, 1]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [1, 1, 1] [] ∧ LexLE [] [])) h)

private theorem k14t7_cover116 : ∀ P ∈ pathPatterns 0 3 [1, 1, 1, 1], HasCheckedCertificate 14 7 ([[], [], [1, 1, 1, 1]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k14t7p67, Certificates.k14t7p67_check⟩

private theorem k14t7_cover117 : ∀ P ∈ pathPatterns 0 2 [1, 1, 1, 2], HasCheckedCertificate 14 7 ([[], [], [1, 1, 1, 2]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k14t7p68, Certificates.k14t7p68_check⟩

private theorem k14t7_cover118 : ∀ P ∈ pathPatterns 0 1 [1, 1, 1, 3], HasCheckedCertificate 14 7 ([[], [], [1, 1, 1, 3]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k14t7p69, Certificates.k14t7p69_check⟩

private theorem k14t7_cover119 : ∀ P ∈ pathPatterns 0 0 [1, 1, 1, 4], HasCheckedCertificate 14 7 ([[], [], [1, 1, 1, 4]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k14t7p70, Certificates.k14t7p70_check⟩

private theorem k14t7_cover120 : ∀ P ∈ pathPatterns 1 3 [1, 1, 2], HasCheckedCertificate 14 7 ([[], [], [1, 1, 2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [1, 1, 2] [] ∧ LexLE [] [])) h)

private theorem k14t7_cover121 : ∀ P ∈ pathPatterns 0 2 [1, 1, 2, 1], HasCheckedCertificate 14 7 ([[], [], [1, 1, 2, 1]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k14t7p71, Certificates.k14t7p71_check⟩

private theorem k14t7_cover122 : ∀ P ∈ pathPatterns 0 1 [1, 1, 2, 2], HasCheckedCertificate 14 7 ([[], [], [1, 1, 2, 2]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k14t7p72, Certificates.k14t7p72_check⟩

private theorem k14t7_cover123 : ∀ P ∈ pathPatterns 0 0 [1, 1, 2, 3], HasCheckedCertificate 14 7 ([[], [], [1, 1, 2, 3]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k14t7p73, Certificates.k14t7p73_check⟩

private theorem k14t7_cover124 : ∀ P ∈ pathPatterns 1 2 [1, 1, 3], HasCheckedCertificate 14 7 ([[], [], [1, 1, 3]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [1, 1, 3] [] ∧ LexLE [] [])) h)

private theorem k14t7_cover125 : ∀ P ∈ pathPatterns 0 1 [1, 1, 3, 1], HasCheckedCertificate 14 7 ([[], [], [1, 1, 3, 1]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k14t7p74, Certificates.k14t7p74_check⟩

private theorem k14t7_cover126 : ∀ P ∈ pathPatterns 0 0 [1, 1, 3, 2], HasCheckedCertificate 14 7 ([[], [], [1, 1, 3, 2]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k14t7p75, Certificates.k14t7p75_check⟩

private theorem k14t7_cover127 : ∀ P ∈ pathPatterns 1 1 [1, 1, 4], HasCheckedCertificate 14 7 ([[], [], [1, 1, 4]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [1, 1, 4] [] ∧ LexLE [] [])) h)

private theorem k14t7_cover128 : ∀ P ∈ pathPatterns 0 0 [1, 1, 4, 1], HasCheckedCertificate 14 7 ([[], [], [1, 1, 4, 1]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k14t7p76, Certificates.k14t7p76_check⟩

private theorem k14t7_cover129 : ∀ P ∈ pathPatterns 1 0 [1, 1, 5], HasCheckedCertificate 14 7 ([[], [], [1, 1, 5]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [1, 1, 5] [] ∧ LexLE [] [])) h)

private theorem k14t7_cover131 : ∀ P ∈ pathPatterns 0 2 [2], HasCheckedCertificate 14 7 ([[], [], [1, 2], [2]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k14t7p77, Certificates.k14t7p77_check⟩

private theorem k14t7_cover132 : ∀ P ∈ pathPatterns 0 1 [3], HasCheckedCertificate 14 7 ([[], [], [1, 2], [3]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k14t7p78, Certificates.k14t7p78_check⟩

private theorem k14t7_cover133 : ∀ P ∈ pathPatterns 0 0 [4], HasCheckedCertificate 14 7 ([[], [], [1, 2], [4]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k14t7p79, Certificates.k14t7p79_check⟩

private theorem k14t7_cover130 : ∀ P ∈ pathPatterns 2 4 [1, 2], HasCheckedCertificate 14 7 ([[], [], [1, 2]] ++ P) := by
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
            exact k14t7_cover131
        · exact by
            intro _
            exact k14t7_cover132
        · exact by
            intro _
            exact k14t7_cover133

private theorem k14t7_cover134 : ∀ P ∈ pathPatterns 1 3 [1, 2, 1], HasCheckedCertificate 14 7 ([[], [], [1, 2, 1]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [1, 2, 1] [] ∧ LexLE [] [])) h)

private theorem k14t7_cover135 : ∀ P ∈ pathPatterns 0 1 [1, 2, 1, 2], HasCheckedCertificate 14 7 ([[], [], [1, 2, 1, 2]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k14t7p80, Certificates.k14t7p80_check⟩

private theorem k14t7_cover136 : ∀ P ∈ pathPatterns 0 0 [1, 2, 1, 3], HasCheckedCertificate 14 7 ([[], [], [1, 2, 1, 3]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k14t7p81, Certificates.k14t7p81_check⟩

private theorem k14t7_cover137 : ∀ P ∈ pathPatterns 1 2 [1, 2, 2], HasCheckedCertificate 14 7 ([[], [], [1, 2, 2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [1, 2, 2] [] ∧ LexLE [] [])) h)

private theorem k14t7_cover138 : ∀ P ∈ pathPatterns 0 1 [1, 2, 2, 1], HasCheckedCertificate 14 7 ([[], [], [1, 2, 2, 1]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k14t7p82, Certificates.k14t7p82_check⟩

private theorem k14t7_cover139 : ∀ P ∈ pathPatterns 0 0 [1, 2, 2, 2], HasCheckedCertificate 14 7 ([[], [], [1, 2, 2, 2]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k14t7p83, Certificates.k14t7p83_check⟩

private theorem k14t7_cover140 : ∀ P ∈ pathPatterns 1 1 [1, 2, 3], HasCheckedCertificate 14 7 ([[], [], [1, 2, 3]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [1, 2, 3] [] ∧ LexLE [] [])) h)

private theorem k14t7_cover141 : ∀ P ∈ pathPatterns 0 0 [1, 2, 3, 1], HasCheckedCertificate 14 7 ([[], [], [1, 2, 3, 1]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k14t7p84, Certificates.k14t7p84_check⟩

private theorem k14t7_cover142 : ∀ P ∈ pathPatterns 1 0 [1, 2, 4], HasCheckedCertificate 14 7 ([[], [], [1, 2, 4]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [1, 2, 4] [] ∧ LexLE [] [])) h)

private theorem k14t7_cover144 : ∀ P ∈ pathPatterns 0 1 [2], HasCheckedCertificate 14 7 ([[], [], [1, 3], [2]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k14t7p85, Certificates.k14t7p85_check⟩

private theorem k14t7_cover145 : ∀ P ∈ pathPatterns 0 0 [3], HasCheckedCertificate 14 7 ([[], [], [1, 3], [3]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k14t7p86, Certificates.k14t7p86_check⟩

private theorem k14t7_cover143 : ∀ P ∈ pathPatterns 2 3 [1, 3], HasCheckedCertificate 14 7 ([[], [], [1, 3]] ++ P) := by
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
            exact k14t7_cover144
        · exact by
            intro _
            exact k14t7_cover145

private theorem k14t7_cover146 : ∀ P ∈ pathPatterns 1 2 [1, 3, 1], HasCheckedCertificate 14 7 ([[], [], [1, 3, 1]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [1, 3, 1] [] ∧ LexLE [] [])) h)

private theorem k14t7_cover147 : ∀ P ∈ pathPatterns 0 0 [1, 3, 1, 2], HasCheckedCertificate 14 7 ([[], [], [1, 3, 1, 2]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k14t7p87, Certificates.k14t7p87_check⟩

private theorem k14t7_cover148 : ∀ P ∈ pathPatterns 1 1 [1, 3, 2], HasCheckedCertificate 14 7 ([[], [], [1, 3, 2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [1, 3, 2] [] ∧ LexLE [] [])) h)

private theorem k14t7_cover149 : ∀ P ∈ pathPatterns 1 0 [1, 3, 3], HasCheckedCertificate 14 7 ([[], [], [1, 3, 3]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [1, 3, 3] [] ∧ LexLE [] [])) h)

private theorem k14t7_cover151 : ∀ P ∈ pathPatterns 0 0 [2], HasCheckedCertificate 14 7 ([[], [], [1, 4], [2]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k14t7p88, Certificates.k14t7p88_check⟩

private theorem k14t7_cover150 : ∀ P ∈ pathPatterns 2 2 [1, 4], HasCheckedCertificate 14 7 ([[], [], [1, 4]] ++ P) := by
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
            exact k14t7_cover151

private theorem k14t7_cover152 : ∀ P ∈ pathPatterns 1 1 [1, 4, 1], HasCheckedCertificate 14 7 ([[], [], [1, 4, 1]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [1, 4, 1] [] ∧ LexLE [] [])) h)

private theorem k14t7_cover153 : ∀ P ∈ pathPatterns 1 0 [1, 4, 2], HasCheckedCertificate 14 7 ([[], [], [1, 4, 2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [1, 4, 2] [] ∧ LexLE [] [])) h)

private theorem k14t7_cover154 : ∀ P ∈ pathPatterns 2 1 [1, 5], HasCheckedCertificate 14 7 ([[], [], [1, 5]] ++ P) := by
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

private theorem k14t7_cover155 : ∀ P ∈ pathPatterns 1 0 [1, 5, 1], HasCheckedCertificate 14 7 ([[], [], [1, 5, 1]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [1, 5, 1] [] ∧ LexLE [] [])) h)

private theorem k14t7_cover156 : ∀ P ∈ pathPatterns 2 0 [1, 6], HasCheckedCertificate 14 7 ([[], [], [1, 6]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [1, 6] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k14t7_seq93 : amountSequenceForall 3 6 (fun tail =>
    (LexLE [] ([1] ++ tail) ∧ LexLE ([1] ++ tail) ([1] ++ tail).reverse) →
    ∀ P ∈ pathPatterns (4 - ([1] ++ tail).length) (7 - ([1] ++ tail).sum) ([1] ++ tail),
      HasCheckedCertificate 14 7 ([[], []] ++ (([1] ++ tail) :: P))) :=
by
  constructor
  · exact by
      intro _
      exact k14t7_cover94
  · intro q
    fin_cases q
    · exact by
        constructor
        · exact by
            intro _
            exact k14t7_cover110
        · intro q
          fin_cases q
          · exact by
              constructor
              · exact by
                  intro _
                  exact k14t7_cover115
              · intro q
                fin_cases q
                · exact by
                    intro _
                    exact k14t7_cover116
                · exact by
                    intro _
                    exact k14t7_cover117
                · exact by
                    intro _
                    exact k14t7_cover118
                · exact by
                    intro _
                    exact k14t7_cover119
          · exact by
              constructor
              · exact by
                  intro _
                  exact k14t7_cover120
              · intro q
                fin_cases q
                · exact by
                    intro _
                    exact k14t7_cover121
                · exact by
                    intro _
                    exact k14t7_cover122
                · exact by
                    intro _
                    exact k14t7_cover123
          · exact by
              constructor
              · exact by
                  intro _
                  exact k14t7_cover124
              · intro q
                fin_cases q
                · exact by
                    intro _
                    exact k14t7_cover125
                · exact by
                    intro _
                    exact k14t7_cover126
          · exact by
              constructor
              · exact by
                  intro _
                  exact k14t7_cover127
              · intro q
                fin_cases q
                · exact by
                    intro _
                    exact k14t7_cover128
          · exact by
              constructor
              · exact by
                  intro _
                  exact k14t7_cover129
              · intro q
                exact Fin.elim0 q
    · exact by
        constructor
        · exact by
            intro _
            exact k14t7_cover130
        · intro q
          fin_cases q
          · exact by
              constructor
              · exact by
                  intro _
                  exact k14t7_cover134
              · intro q
                fin_cases q
                · exact by
                    intro h
                    exact False.elim ((by decide : ¬ (LexLE [] [1, 2, 1, 1] ∧ LexLE [1, 2, 1, 1] [1, 1, 2, 1])) h)
                · exact by
                    intro _
                    exact k14t7_cover135
                · exact by
                    intro _
                    exact k14t7_cover136
          · exact by
              constructor
              · exact by
                  intro _
                  exact k14t7_cover137
              · intro q
                fin_cases q
                · exact by
                    intro _
                    exact k14t7_cover138
                · exact by
                    intro _
                    exact k14t7_cover139
          · exact by
              constructor
              · exact by
                  intro _
                  exact k14t7_cover140
              · intro q
                fin_cases q
                · exact by
                    intro _
                    exact k14t7_cover141
          · exact by
              constructor
              · exact by
                  intro _
                  exact k14t7_cover142
              · intro q
                exact Fin.elim0 q
    · exact by
        constructor
        · exact by
            intro _
            exact k14t7_cover143
        · intro q
          fin_cases q
          · exact by
              constructor
              · exact by
                  intro _
                  exact k14t7_cover146
              · intro q
                fin_cases q
                · exact by
                    intro h
                    exact False.elim ((by decide : ¬ (LexLE [] [1, 3, 1, 1] ∧ LexLE [1, 3, 1, 1] [1, 1, 3, 1])) h)
                · exact by
                    intro _
                    exact k14t7_cover147
          · exact by
              constructor
              · exact by
                  intro _
                  exact k14t7_cover148
              · intro q
                fin_cases q
                · exact by
                    intro h
                    exact False.elim ((by decide : ¬ (LexLE [] [1, 3, 2, 1] ∧ LexLE [1, 3, 2, 1] [1, 2, 3, 1])) h)
          · exact by
              constructor
              · exact by
                  intro _
                  exact k14t7_cover149
              · intro q
                exact Fin.elim0 q
    · exact by
        constructor
        · exact by
            intro _
            exact k14t7_cover150
        · intro q
          fin_cases q
          · exact by
              constructor
              · exact by
                  intro _
                  exact k14t7_cover152
              · intro q
                fin_cases q
                · exact by
                    intro h
                    exact False.elim ((by decide : ¬ (LexLE [] [1, 4, 1, 1] ∧ LexLE [1, 4, 1, 1] [1, 1, 4, 1])) h)
          · exact by
              constructor
              · exact by
                  intro _
                  exact k14t7_cover153
              · intro q
                exact Fin.elim0 q
    · exact by
        constructor
        · exact by
            intro _
            exact k14t7_cover154
        · intro q
          fin_cases q
          · exact by
              constructor
              · exact by
                  intro _
                  exact k14t7_cover155
              · intro q
                exact Fin.elim0 q
    · exact by
        constructor
        · exact by
            intro _
            exact k14t7_cover156
        · intro q
          exact Fin.elim0 q

private theorem k14t7_cover159 : ∀ P ∈ pathPatterns 1 3 [2], HasCheckedCertificate 14 7 ([[], [], [2], [2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [2] [] ∧ LexLE [] [])) h)

private theorem k14t7_cover160 : ∀ P ∈ pathPatterns 0 1 [2, 2], HasCheckedCertificate 14 7 ([[], [], [2], [2, 2]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k14t7p89, Certificates.k14t7p89_check⟩

private theorem k14t7_cover161 : ∀ P ∈ pathPatterns 0 0 [2, 3], HasCheckedCertificate 14 7 ([[], [], [2], [2, 3]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k14t7p90, Certificates.k14t7p90_check⟩

private theorem k14t7_cover162 : ∀ P ∈ pathPatterns 1 2 [3], HasCheckedCertificate 14 7 ([[], [], [2], [3]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [3] [] ∧ LexLE [] [])) h)

private theorem k14t7_cover163 : ∀ P ∈ pathPatterns 1 1 [4], HasCheckedCertificate 14 7 ([[], [], [2], [4]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [4] [] ∧ LexLE [] [])) h)

private theorem k14t7_cover164 : ∀ P ∈ pathPatterns 1 0 [5], HasCheckedCertificate 14 7 ([[], [], [2], [5]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [5] [] ∧ LexLE [] [])) h)

private theorem k14t7_cover158 : ∀ P ∈ pathPatterns 3 5 [2], HasCheckedCertificate 14 7 ([[], [], [2]] ++ P) := by
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
                exact k14t7_cover159
            · intro q
              fin_cases q
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [2] [2, 1] ∧ LexLE [2, 1] [1, 2])) h)
              · exact by
                  intro _
                  exact k14t7_cover160
              · exact by
                  intro _
                  exact k14t7_cover161
        · exact by
            constructor
            · exact by
                intro _
                exact k14t7_cover162
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
                exact k14t7_cover163
            · intro q
              fin_cases q
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [2] [4, 1] ∧ LexLE [4, 1] [1, 4])) h)
        · exact by
            constructor
            · exact by
                intro _
                exact k14t7_cover164
            · intro q
              exact Fin.elim0 q

private theorem k14t7_cover165 : ∀ P ∈ pathPatterns 0 1 [2, 1, 1, 2], HasCheckedCertificate 14 7 ([[], [], [2, 1, 1, 2]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k14t7p91, Certificates.k14t7p91_check⟩

private theorem k14t7_cover166 : ∀ P ∈ pathPatterns 0 0 [2, 1, 1, 3], HasCheckedCertificate 14 7 ([[], [], [2, 1, 1, 3]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k14t7p92, Certificates.k14t7p92_check⟩

private theorem k14t7_cover167 : ∀ P ∈ pathPatterns 1 2 [2, 1, 2], HasCheckedCertificate 14 7 ([[], [], [2, 1, 2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [2, 1, 2] [] ∧ LexLE [] [])) h)

private theorem k14t7_cover168 : ∀ P ∈ pathPatterns 0 0 [2, 1, 2, 2], HasCheckedCertificate 14 7 ([[], [], [2, 1, 2, 2]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k14t7p93, Certificates.k14t7p93_check⟩

private theorem k14t7_cover169 : ∀ P ∈ pathPatterns 1 1 [2, 1, 3], HasCheckedCertificate 14 7 ([[], [], [2, 1, 3]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [2, 1, 3] [] ∧ LexLE [] [])) h)

private theorem k14t7_cover170 : ∀ P ∈ pathPatterns 1 0 [2, 1, 4], HasCheckedCertificate 14 7 ([[], [], [2, 1, 4]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [2, 1, 4] [] ∧ LexLE [] [])) h)

private theorem k14t7_cover172 : ∀ P ∈ pathPatterns 0 0 [3], HasCheckedCertificate 14 7 ([[], [], [2, 2], [3]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k14t7p94, Certificates.k14t7p94_check⟩

private theorem k14t7_cover171 : ∀ P ∈ pathPatterns 2 3 [2, 2], HasCheckedCertificate 14 7 ([[], [], [2, 2]] ++ P) := by
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
            exact k14t7_cover172

private theorem k14t7_cover173 : ∀ P ∈ pathPatterns 1 1 [2, 2, 2], HasCheckedCertificate 14 7 ([[], [], [2, 2, 2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [2, 2, 2] [] ∧ LexLE [] [])) h)

private theorem k14t7_cover174 : ∀ P ∈ pathPatterns 1 0 [2, 2, 3], HasCheckedCertificate 14 7 ([[], [], [2, 2, 3]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [2, 2, 3] [] ∧ LexLE [] [])) h)

private theorem k14t7_cover175 : ∀ P ∈ pathPatterns 2 2 [2, 3], HasCheckedCertificate 14 7 ([[], [], [2, 3]] ++ P) := by
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

private theorem k14t7_cover176 : ∀ P ∈ pathPatterns 1 0 [2, 3, 2], HasCheckedCertificate 14 7 ([[], [], [2, 3, 2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [2, 3, 2] [] ∧ LexLE [] [])) h)

private theorem k14t7_cover177 : ∀ P ∈ pathPatterns 2 1 [2, 4], HasCheckedCertificate 14 7 ([[], [], [2, 4]] ++ P) := by
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

private theorem k14t7_cover178 : ∀ P ∈ pathPatterns 2 0 [2, 5], HasCheckedCertificate 14 7 ([[], [], [2, 5]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [2, 5] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k14t7_seq157 : amountSequenceForall 3 5 (fun tail =>
    (LexLE [] ([2] ++ tail) ∧ LexLE ([2] ++ tail) ([2] ++ tail).reverse) →
    ∀ P ∈ pathPatterns (4 - ([2] ++ tail).length) (7 - ([2] ++ tail).sum) ([2] ++ tail),
      HasCheckedCertificate 14 7 ([[], []] ++ (([2] ++ tail) :: P))) :=
by
  constructor
  · exact by
      intro _
      exact k14t7_cover158
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
                    exact k14t7_cover165
                · exact by
                    intro _
                    exact k14t7_cover166
          · exact by
              constructor
              · exact by
                  intro _
                  exact k14t7_cover167
              · intro q
                fin_cases q
                · exact by
                    intro h
                    exact False.elim ((by decide : ¬ (LexLE [] [2, 1, 2, 1] ∧ LexLE [2, 1, 2, 1] [1, 2, 1, 2])) h)
                · exact by
                    intro _
                    exact k14t7_cover168
          · exact by
              constructor
              · exact by
                  intro _
                  exact k14t7_cover169
              · intro q
                fin_cases q
                · exact by
                    intro h
                    exact False.elim ((by decide : ¬ (LexLE [] [2, 1, 3, 1] ∧ LexLE [2, 1, 3, 1] [1, 3, 1, 2])) h)
          · exact by
              constructor
              · exact by
                  intro _
                  exact k14t7_cover170
              · intro q
                exact Fin.elim0 q
    · exact by
        constructor
        · exact by
            intro _
            exact k14t7_cover171
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
              constructor
              · exact by
                  intro _
                  exact k14t7_cover173
              · intro q
                fin_cases q
                · exact by
                    intro h
                    exact False.elim ((by decide : ¬ (LexLE [] [2, 2, 2, 1] ∧ LexLE [2, 2, 2, 1] [1, 2, 2, 2])) h)
          · exact by
              constructor
              · exact by
                  intro _
                  exact k14t7_cover174
              · intro q
                exact Fin.elim0 q
    · exact by
        constructor
        · exact by
            intro _
            exact k14t7_cover175
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
              constructor
              · exact by
                  intro _
                  exact k14t7_cover176
              · intro q
                exact Fin.elim0 q
    · exact by
        constructor
        · exact by
            intro _
            exact k14t7_cover177
        · intro q
          fin_cases q
          · exact by
              constructor
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [] [2, 4, 1] ∧ LexLE [2, 4, 1] [1, 4, 2])) h)
              · intro q
                exact Fin.elim0 q
    · exact by
        constructor
        · exact by
            intro _
            exact k14t7_cover178
        · intro q
          exact Fin.elim0 q

private theorem k14t7_cover180 : ∀ P ∈ pathPatterns 1 1 [3], HasCheckedCertificate 14 7 ([[], [], [3], [3]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [3] [] ∧ LexLE [] [])) h)

private theorem k14t7_cover181 : ∀ P ∈ pathPatterns 1 0 [4], HasCheckedCertificate 14 7 ([[], [], [3], [4]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [4] [] ∧ LexLE [] [])) h)

private theorem k14t7_cover179 : ∀ P ∈ pathPatterns 3 4 [3], HasCheckedCertificate 14 7 ([[], [], [3]] ++ P) := by
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
                exact k14t7_cover180
            · intro q
              fin_cases q
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [3] [3, 1] ∧ LexLE [3, 1] [1, 3])) h)
        · exact by
            constructor
            · exact by
                intro _
                exact k14t7_cover181
            · intro q
              exact Fin.elim0 q

private theorem k14t7_cover182 : ∀ P ∈ pathPatterns 1 0 [3, 1, 3], HasCheckedCertificate 14 7 ([[], [], [3, 1, 3]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [3, 1, 3] [] ∧ LexLE [] [])) h)

private theorem k14t7_cover183 : ∀ P ∈ pathPatterns 2 1 [3, 3], HasCheckedCertificate 14 7 ([[], [], [3, 3]] ++ P) := by
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

private theorem k14t7_cover184 : ∀ P ∈ pathPatterns 2 0 [3, 4], HasCheckedCertificate 14 7 ([[], [], [3, 4]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [3, 4] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k14t7_cover185 : ∀ P ∈ pathPatterns 3 3 [4], HasCheckedCertificate 14 7 ([[], [], [4]] ++ P) := by
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

private theorem k14t7_cover186 : ∀ P ∈ pathPatterns 3 2 [5], HasCheckedCertificate 14 7 ([[], [], [5]] ++ P) := by
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

private theorem k14t7_cover187 : ∀ P ∈ pathPatterns 3 1 [6], HasCheckedCertificate 14 7 ([[], [], [6]] ++ P) := by
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

private theorem k14t7_cover188 : ∀ P ∈ pathPatterns 3 0 [7], HasCheckedCertificate 14 7 ([[], [], [7]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [7] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k14t7_seq6 : amountSequenceForall 4 7 (fun tail =>
    (LexLE [] ([] ++ tail) ∧ LexLE ([] ++ tail) ([] ++ tail).reverse) →
    ∀ P ∈ pathPatterns (4 - ([] ++ tail).length) (7 - ([] ++ tail).sum) ([] ++ tail),
      HasCheckedCertificate 14 7 ([[], []] ++ (([] ++ tail) :: P))) :=
by
  constructor
  · exact by
      intro _
      exact k14t7_cover7
  · intro q
    fin_cases q
    · exact k14t7_seq93

    · exact k14t7_seq157

    · exact by
        constructor
        · exact by
            intro _
            exact k14t7_cover179
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
                    constructor
                    · exact by
                        intro _
                        exact k14t7_cover182
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
                    constructor
                    · exact by
                        intro h
                        exact False.elim ((by decide : ¬ (LexLE [] [3, 2, 2] ∧ LexLE [3, 2, 2] [2, 2, 3])) h)
                    · intro q
                      exact Fin.elim0 q
          · exact by
              constructor
              · exact by
                  intro _
                  exact k14t7_cover183
              · intro q
                fin_cases q
                · exact by
                    constructor
                    · exact by
                        intro h
                        exact False.elim ((by decide : ¬ (LexLE [] [3, 3, 1] ∧ LexLE [3, 3, 1] [1, 3, 3])) h)
                    · intro q
                      exact Fin.elim0 q
          · exact by
              constructor
              · exact by
                  intro _
                  exact k14t7_cover184
              · intro q
                exact Fin.elim0 q
    · exact by
        constructor
        · exact by
            intro _
            exact k14t7_cover185
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
                    constructor
                    · exact by
                        intro h
                        exact False.elim ((by decide : ¬ (LexLE [] [4, 1, 2] ∧ LexLE [4, 1, 2] [2, 1, 4])) h)
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
                      exact Fin.elim0 q
          · exact by
              constructor
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [] [4, 3] ∧ LexLE [4, 3] [3, 4])) h)
              · intro q
                exact Fin.elim0 q
    · exact by
        constructor
        · exact by
            intro _
            exact k14t7_cover186
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
                      exact Fin.elim0 q
          · exact by
              constructor
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [] [5, 2] ∧ LexLE [5, 2] [2, 5])) h)
              · intro q
                exact Fin.elim0 q
    · exact by
        constructor
        · exact by
            intro _
            exact k14t7_cover187
        · intro q
          fin_cases q
          · exact by
              constructor
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [] [6, 1] ∧ LexLE [6, 1] [1, 6])) h)
              · intro q
                exact Fin.elim0 q
    · exact by
        constructor
        · exact by
            intro _
            exact k14t7_cover188
        · intro q
          exact Fin.elim0 q

private theorem k14t7_cover5 : ∀ P ∈ pathPatterns 5 7 [], HasCheckedCertificate 14 7 ([[], []] ++ P) := by
  apply pathPatterns_forall_step
  exact k14t7_seq6


private theorem k14t7_cover193 : ∀ P ∈ pathPatterns 0 4 [1], HasCheckedCertificate 14 7 ([[], [1], [1], [1]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k14t7p95, Certificates.k14t7p95_check⟩

private theorem k14t7_cover194 : ∀ P ∈ pathPatterns 0 3 [2], HasCheckedCertificate 14 7 ([[], [1], [1], [2]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k14t7p96, Certificates.k14t7p96_check⟩

private theorem k14t7_cover195 : ∀ P ∈ pathPatterns 0 2 [3], HasCheckedCertificate 14 7 ([[], [1], [1], [3]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k14t7p97, Certificates.k14t7p97_check⟩

private theorem k14t7_cover196 : ∀ P ∈ pathPatterns 0 1 [4], HasCheckedCertificate 14 7 ([[], [1], [1], [4]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k14t7p98, Certificates.k14t7p98_check⟩

private theorem k14t7_cover197 : ∀ P ∈ pathPatterns 0 0 [5], HasCheckedCertificate 14 7 ([[], [1], [1], [5]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k14t7p99, Certificates.k14t7p99_check⟩

private theorem k14t7_cover192 : ∀ P ∈ pathPatterns 2 5 [1], HasCheckedCertificate 14 7 ([[], [1], [1]] ++ P) := by
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
            exact k14t7_cover193
        · exact by
            intro _
            exact k14t7_cover194
        · exact by
            intro _
            exact k14t7_cover195
        · exact by
            intro _
            exact k14t7_cover196
        · exact by
            intro _
            exact k14t7_cover197

private theorem k14t7_cover198 : ∀ P ∈ pathPatterns 1 4 [1, 1], HasCheckedCertificate 14 7 ([[], [1], [1, 1]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [1, 1] [] ∧ LexLE [] [])) h)

private theorem k14t7_cover199 : ∀ P ∈ pathPatterns 0 3 [1, 1, 1], HasCheckedCertificate 14 7 ([[], [1], [1, 1, 1]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k14t7p100, Certificates.k14t7p100_check⟩

private theorem k14t7_cover200 : ∀ P ∈ pathPatterns 0 2 [1, 1, 2], HasCheckedCertificate 14 7 ([[], [1], [1, 1, 2]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k14t7p101, Certificates.k14t7p101_check⟩

private theorem k14t7_cover201 : ∀ P ∈ pathPatterns 0 1 [1, 1, 3], HasCheckedCertificate 14 7 ([[], [1], [1, 1, 3]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k14t7p102, Certificates.k14t7p102_check⟩

private theorem k14t7_cover202 : ∀ P ∈ pathPatterns 0 0 [1, 1, 4], HasCheckedCertificate 14 7 ([[], [1], [1, 1, 4]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k14t7p103, Certificates.k14t7p103_check⟩

private theorem k14t7_cover203 : ∀ P ∈ pathPatterns 1 3 [1, 2], HasCheckedCertificate 14 7 ([[], [1], [1, 2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [1, 2] [] ∧ LexLE [] [])) h)

private theorem k14t7_cover204 : ∀ P ∈ pathPatterns 0 2 [1, 2, 1], HasCheckedCertificate 14 7 ([[], [1], [1, 2, 1]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k14t7p104, Certificates.k14t7p104_check⟩

private theorem k14t7_cover205 : ∀ P ∈ pathPatterns 0 1 [1, 2, 2], HasCheckedCertificate 14 7 ([[], [1], [1, 2, 2]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k14t7p105, Certificates.k14t7p105_check⟩

private theorem k14t7_cover206 : ∀ P ∈ pathPatterns 0 0 [1, 2, 3], HasCheckedCertificate 14 7 ([[], [1], [1, 2, 3]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k14t7p106, Certificates.k14t7p106_check⟩

private theorem k14t7_cover207 : ∀ P ∈ pathPatterns 1 2 [1, 3], HasCheckedCertificate 14 7 ([[], [1], [1, 3]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [1, 3] [] ∧ LexLE [] [])) h)

private theorem k14t7_cover208 : ∀ P ∈ pathPatterns 0 1 [1, 3, 1], HasCheckedCertificate 14 7 ([[], [1], [1, 3, 1]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k14t7p107, Certificates.k14t7p107_check⟩

private theorem k14t7_cover209 : ∀ P ∈ pathPatterns 0 0 [1, 3, 2], HasCheckedCertificate 14 7 ([[], [1], [1, 3, 2]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k14t7p108, Certificates.k14t7p108_check⟩

private theorem k14t7_cover210 : ∀ P ∈ pathPatterns 1 1 [1, 4], HasCheckedCertificate 14 7 ([[], [1], [1, 4]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [1, 4] [] ∧ LexLE [] [])) h)

private theorem k14t7_cover211 : ∀ P ∈ pathPatterns 0 0 [1, 4, 1], HasCheckedCertificate 14 7 ([[], [1], [1, 4, 1]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k14t7p109, Certificates.k14t7p109_check⟩

private theorem k14t7_cover212 : ∀ P ∈ pathPatterns 1 0 [1, 5], HasCheckedCertificate 14 7 ([[], [1], [1, 5]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [1, 5] [] ∧ LexLE [] [])) h)

private theorem k14t7_cover214 : ∀ P ∈ pathPatterns 0 2 [2], HasCheckedCertificate 14 7 ([[], [1], [2], [2]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k14t7p110, Certificates.k14t7p110_check⟩

private theorem k14t7_cover215 : ∀ P ∈ pathPatterns 0 1 [3], HasCheckedCertificate 14 7 ([[], [1], [2], [3]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k14t7p111, Certificates.k14t7p111_check⟩

private theorem k14t7_cover216 : ∀ P ∈ pathPatterns 0 0 [4], HasCheckedCertificate 14 7 ([[], [1], [2], [4]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k14t7p112, Certificates.k14t7p112_check⟩

private theorem k14t7_cover213 : ∀ P ∈ pathPatterns 2 4 [2], HasCheckedCertificate 14 7 ([[], [1], [2]] ++ P) := by
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
            exact k14t7_cover214
        · exact by
            intro _
            exact k14t7_cover215
        · exact by
            intro _
            exact k14t7_cover216

private theorem k14t7_cover217 : ∀ P ∈ pathPatterns 0 1 [2, 1, 2], HasCheckedCertificate 14 7 ([[], [1], [2, 1, 2]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k14t7p113, Certificates.k14t7p113_check⟩

private theorem k14t7_cover218 : ∀ P ∈ pathPatterns 0 0 [2, 1, 3], HasCheckedCertificate 14 7 ([[], [1], [2, 1, 3]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k14t7p114, Certificates.k14t7p114_check⟩

private theorem k14t7_cover219 : ∀ P ∈ pathPatterns 1 2 [2, 2], HasCheckedCertificate 14 7 ([[], [1], [2, 2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [2, 2] [] ∧ LexLE [] [])) h)

private theorem k14t7_cover220 : ∀ P ∈ pathPatterns 0 0 [2, 2, 2], HasCheckedCertificate 14 7 ([[], [1], [2, 2, 2]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k14t7p115, Certificates.k14t7p115_check⟩

private theorem k14t7_cover221 : ∀ P ∈ pathPatterns 1 1 [2, 3], HasCheckedCertificate 14 7 ([[], [1], [2, 3]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [2, 3] [] ∧ LexLE [] [])) h)

private theorem k14t7_cover222 : ∀ P ∈ pathPatterns 1 0 [2, 4], HasCheckedCertificate 14 7 ([[], [1], [2, 4]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [2, 4] [] ∧ LexLE [] [])) h)

private theorem k14t7_cover224 : ∀ P ∈ pathPatterns 0 0 [3], HasCheckedCertificate 14 7 ([[], [1], [3], [3]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k14t7p116, Certificates.k14t7p116_check⟩

private theorem k14t7_cover223 : ∀ P ∈ pathPatterns 2 3 [3], HasCheckedCertificate 14 7 ([[], [1], [3]] ++ P) := by
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
            exact k14t7_cover224

private theorem k14t7_cover225 : ∀ P ∈ pathPatterns 1 0 [3, 3], HasCheckedCertificate 14 7 ([[], [1], [3, 3]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [3, 3] [] ∧ LexLE [] [])) h)

private theorem k14t7_cover226 : ∀ P ∈ pathPatterns 2 2 [4], HasCheckedCertificate 14 7 ([[], [1], [4]] ++ P) := by
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

private theorem k14t7_cover227 : ∀ P ∈ pathPatterns 2 1 [5], HasCheckedCertificate 14 7 ([[], [1], [5]] ++ P) := by
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

private theorem k14t7_cover228 : ∀ P ∈ pathPatterns 2 0 [6], HasCheckedCertificate 14 7 ([[], [1], [6]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [6] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k14t7_seq191 : amountSequenceForall 3 6 (fun tail =>
    (LexLE [1] ([] ++ tail) ∧ LexLE ([] ++ tail) ([] ++ tail).reverse) →
    ∀ P ∈ pathPatterns (3 - ([] ++ tail).length) (6 - ([] ++ tail).sum) ([] ++ tail),
      HasCheckedCertificate 14 7 ([[], [1]] ++ (([] ++ tail) :: P))) :=
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
            exact k14t7_cover192
        · intro q
          fin_cases q
          · exact by
              constructor
              · exact by
                  intro _
                  exact k14t7_cover198
              · intro q
                fin_cases q
                · exact by
                    intro _
                    exact k14t7_cover199
                · exact by
                    intro _
                    exact k14t7_cover200
                · exact by
                    intro _
                    exact k14t7_cover201
                · exact by
                    intro _
                    exact k14t7_cover202
          · exact by
              constructor
              · exact by
                  intro _
                  exact k14t7_cover203
              · intro q
                fin_cases q
                · exact by
                    intro _
                    exact k14t7_cover204
                · exact by
                    intro _
                    exact k14t7_cover205
                · exact by
                    intro _
                    exact k14t7_cover206
          · exact by
              constructor
              · exact by
                  intro _
                  exact k14t7_cover207
              · intro q
                fin_cases q
                · exact by
                    intro _
                    exact k14t7_cover208
                · exact by
                    intro _
                    exact k14t7_cover209
          · exact by
              constructor
              · exact by
                  intro _
                  exact k14t7_cover210
              · intro q
                fin_cases q
                · exact by
                    intro _
                    exact k14t7_cover211
          · exact by
              constructor
              · exact by
                  intro _
                  exact k14t7_cover212
              · intro q
                exact Fin.elim0 q
    · exact by
        constructor
        · exact by
            intro _
            exact k14t7_cover213
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
                    exact k14t7_cover217
                · exact by
                    intro _
                    exact k14t7_cover218
          · exact by
              constructor
              · exact by
                  intro _
                  exact k14t7_cover219
              · intro q
                fin_cases q
                · exact by
                    intro h
                    exact False.elim ((by decide : ¬ (LexLE [1] [2, 2, 1] ∧ LexLE [2, 2, 1] [1, 2, 2])) h)
                · exact by
                    intro _
                    exact k14t7_cover220
          · exact by
              constructor
              · exact by
                  intro _
                  exact k14t7_cover221
              · intro q
                fin_cases q
                · exact by
                    intro h
                    exact False.elim ((by decide : ¬ (LexLE [1] [2, 3, 1] ∧ LexLE [2, 3, 1] [1, 3, 2])) h)
          · exact by
              constructor
              · exact by
                  intro _
                  exact k14t7_cover222
              · intro q
                exact Fin.elim0 q
    · exact by
        constructor
        · exact by
            intro _
            exact k14t7_cover223
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
                  exact k14t7_cover225
              · intro q
                exact Fin.elim0 q
    · exact by
        constructor
        · exact by
            intro _
            exact k14t7_cover226
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
            exact k14t7_cover227
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
            exact k14t7_cover228
        · intro q
          exact Fin.elim0 q

private theorem k14t7_cover190 : ∀ P ∈ pathPatterns 4 6 [1], HasCheckedCertificate 14 7 ([[], [1]] ++ P) := by
  apply pathPatterns_forall_step
  exact k14t7_seq191


private theorem k14t7_cover231 : ∀ P ∈ pathPatterns 0 3 [1, 1], HasCheckedCertificate 14 7 ([[], [1, 1], [1, 1]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k14t7p117, Certificates.k14t7p117_check⟩

private theorem k14t7_cover232 : ∀ P ∈ pathPatterns 0 2 [1, 2], HasCheckedCertificate 14 7 ([[], [1, 1], [1, 2]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k14t7p118, Certificates.k14t7p118_check⟩

private theorem k14t7_cover233 : ∀ P ∈ pathPatterns 0 1 [1, 3], HasCheckedCertificate 14 7 ([[], [1, 1], [1, 3]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k14t7p119, Certificates.k14t7p119_check⟩

private theorem k14t7_cover234 : ∀ P ∈ pathPatterns 0 0 [1, 4], HasCheckedCertificate 14 7 ([[], [1, 1], [1, 4]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k14t7p120, Certificates.k14t7p120_check⟩

private theorem k14t7_cover235 : ∀ P ∈ pathPatterns 1 3 [2], HasCheckedCertificate 14 7 ([[], [1, 1], [2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [2] [] ∧ LexLE [] [])) h)

private theorem k14t7_cover236 : ∀ P ∈ pathPatterns 0 1 [2, 2], HasCheckedCertificate 14 7 ([[], [1, 1], [2, 2]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k14t7p121, Certificates.k14t7p121_check⟩

private theorem k14t7_cover237 : ∀ P ∈ pathPatterns 0 0 [2, 3], HasCheckedCertificate 14 7 ([[], [1, 1], [2, 3]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k14t7p122, Certificates.k14t7p122_check⟩

private theorem k14t7_cover238 : ∀ P ∈ pathPatterns 1 2 [3], HasCheckedCertificate 14 7 ([[], [1, 1], [3]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [3] [] ∧ LexLE [] [])) h)

private theorem k14t7_cover239 : ∀ P ∈ pathPatterns 1 1 [4], HasCheckedCertificate 14 7 ([[], [1, 1], [4]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [4] [] ∧ LexLE [] [])) h)

private theorem k14t7_cover240 : ∀ P ∈ pathPatterns 1 0 [5], HasCheckedCertificate 14 7 ([[], [1, 1], [5]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [5] [] ∧ LexLE [] [])) h)

private theorem k14t7_cover230 : ∀ P ∈ pathPatterns 3 5 [1, 1], HasCheckedCertificate 14 7 ([[], [1, 1]] ++ P) := by
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
                  exact k14t7_cover231
              · exact by
                  intro _
                  exact k14t7_cover232
              · exact by
                  intro _
                  exact k14t7_cover233
              · exact by
                  intro _
                  exact k14t7_cover234
        · exact by
            constructor
            · exact by
                intro _
                exact k14t7_cover235
            · intro q
              fin_cases q
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [1, 1] [2, 1] ∧ LexLE [2, 1] [1, 2])) h)
              · exact by
                  intro _
                  exact k14t7_cover236
              · exact by
                  intro _
                  exact k14t7_cover237
        · exact by
            constructor
            · exact by
                intro _
                exact k14t7_cover238
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
                exact k14t7_cover239
            · intro q
              fin_cases q
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [1, 1] [4, 1] ∧ LexLE [4, 1] [1, 4])) h)
        · exact by
            constructor
            · exact by
                intro _
                exact k14t7_cover240
            · intro q
              exact Fin.elim0 q

private theorem k14t7_cover242 : ∀ P ∈ pathPatterns 0 2 [2], HasCheckedCertificate 14 7 ([[], [1, 1, 1], [2]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k14t7p123, Certificates.k14t7p123_check⟩

private theorem k14t7_cover243 : ∀ P ∈ pathPatterns 0 1 [3], HasCheckedCertificate 14 7 ([[], [1, 1, 1], [3]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k14t7p124, Certificates.k14t7p124_check⟩

private theorem k14t7_cover244 : ∀ P ∈ pathPatterns 0 0 [4], HasCheckedCertificate 14 7 ([[], [1, 1, 1], [4]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k14t7p125, Certificates.k14t7p125_check⟩

private theorem k14t7_cover241 : ∀ P ∈ pathPatterns 2 4 [1, 1, 1], HasCheckedCertificate 14 7 ([[], [1, 1, 1]] ++ P) := by
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
            exact k14t7_cover242
        · exact by
            intro _
            exact k14t7_cover243
        · exact by
            intro _
            exact k14t7_cover244

private theorem k14t7_cover245 : ∀ P ∈ pathPatterns 1 3 [1, 1, 1, 1], HasCheckedCertificate 14 7 ([[], [1, 1, 1, 1]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [1, 1, 1, 1] [] ∧ LexLE [] [])) h)

private theorem k14t7_cover246 : ∀ P ∈ pathPatterns 0 2 [1, 1, 1, 1, 1], HasCheckedCertificate 14 7 ([[], [1, 1, 1, 1, 1]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k14t7p126, Certificates.k14t7p126_check⟩

private theorem k14t7_cover247 : ∀ P ∈ pathPatterns 0 1 [1, 1, 1, 1, 2], HasCheckedCertificate 14 7 ([[], [1, 1, 1, 1, 2]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k14t7p127, Certificates.k14t7p127_check⟩

private theorem k14t7_cover248 : ∀ P ∈ pathPatterns 0 0 [1, 1, 1, 1, 3], HasCheckedCertificate 14 7 ([[], [1, 1, 1, 1, 3]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k14t7p128, Certificates.k14t7p128_check⟩

private theorem k14t7_cover249 : ∀ P ∈ pathPatterns 1 2 [1, 1, 1, 2], HasCheckedCertificate 14 7 ([[], [1, 1, 1, 2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [1, 1, 1, 2] [] ∧ LexLE [] [])) h)

private theorem k14t7_cover250 : ∀ P ∈ pathPatterns 0 1 [1, 1, 1, 2, 1], HasCheckedCertificate 14 7 ([[], [1, 1, 1, 2, 1]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k14t7p129, Certificates.k14t7p129_check⟩

private theorem k14t7_cover251 : ∀ P ∈ pathPatterns 0 0 [1, 1, 1, 2, 2], HasCheckedCertificate 14 7 ([[], [1, 1, 1, 2, 2]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k14t7p130, Certificates.k14t7p130_check⟩

private theorem k14t7_cover252 : ∀ P ∈ pathPatterns 1 1 [1, 1, 1, 3], HasCheckedCertificate 14 7 ([[], [1, 1, 1, 3]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [1, 1, 1, 3] [] ∧ LexLE [] [])) h)

private theorem k14t7_cover253 : ∀ P ∈ pathPatterns 0 0 [1, 1, 1, 3, 1], HasCheckedCertificate 14 7 ([[], [1, 1, 1, 3, 1]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k14t7p131, Certificates.k14t7p131_check⟩

private theorem k14t7_cover254 : ∀ P ∈ pathPatterns 1 0 [1, 1, 1, 4], HasCheckedCertificate 14 7 ([[], [1, 1, 1, 4]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [1, 1, 1, 4] [] ∧ LexLE [] [])) h)

private theorem k14t7_cover256 : ∀ P ∈ pathPatterns 0 1 [2], HasCheckedCertificate 14 7 ([[], [1, 1, 2], [2]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k14t7p132, Certificates.k14t7p132_check⟩

private theorem k14t7_cover257 : ∀ P ∈ pathPatterns 0 0 [3], HasCheckedCertificate 14 7 ([[], [1, 1, 2], [3]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k14t7p133, Certificates.k14t7p133_check⟩

private theorem k14t7_cover255 : ∀ P ∈ pathPatterns 2 3 [1, 1, 2], HasCheckedCertificate 14 7 ([[], [1, 1, 2]] ++ P) := by
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
            exact k14t7_cover256
        · exact by
            intro _
            exact k14t7_cover257

private theorem k14t7_cover258 : ∀ P ∈ pathPatterns 1 2 [1, 1, 2, 1], HasCheckedCertificate 14 7 ([[], [1, 1, 2, 1]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [1, 1, 2, 1] [] ∧ LexLE [] [])) h)

private theorem k14t7_cover259 : ∀ P ∈ pathPatterns 0 1 [1, 1, 2, 1, 1], HasCheckedCertificate 14 7 ([[], [1, 1, 2, 1, 1]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k14t7p134, Certificates.k14t7p134_check⟩

private theorem k14t7_cover260 : ∀ P ∈ pathPatterns 0 0 [1, 1, 2, 1, 2], HasCheckedCertificate 14 7 ([[], [1, 1, 2, 1, 2]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k14t7p135, Certificates.k14t7p135_check⟩

private theorem k14t7_cover261 : ∀ P ∈ pathPatterns 1 1 [1, 1, 2, 2], HasCheckedCertificate 14 7 ([[], [1, 1, 2, 2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [1, 1, 2, 2] [] ∧ LexLE [] [])) h)

private theorem k14t7_cover262 : ∀ P ∈ pathPatterns 0 0 [1, 1, 2, 2, 1], HasCheckedCertificate 14 7 ([[], [1, 1, 2, 2, 1]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k14t7p136, Certificates.k14t7p136_check⟩

private theorem k14t7_cover263 : ∀ P ∈ pathPatterns 1 0 [1, 1, 2, 3], HasCheckedCertificate 14 7 ([[], [1, 1, 2, 3]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [1, 1, 2, 3] [] ∧ LexLE [] [])) h)

private theorem k14t7_cover265 : ∀ P ∈ pathPatterns 0 0 [2], HasCheckedCertificate 14 7 ([[], [1, 1, 3], [2]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k14t7p137, Certificates.k14t7p137_check⟩

private theorem k14t7_cover264 : ∀ P ∈ pathPatterns 2 2 [1, 1, 3], HasCheckedCertificate 14 7 ([[], [1, 1, 3]] ++ P) := by
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
            exact k14t7_cover265

private theorem k14t7_cover266 : ∀ P ∈ pathPatterns 1 1 [1, 1, 3, 1], HasCheckedCertificate 14 7 ([[], [1, 1, 3, 1]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [1, 1, 3, 1] [] ∧ LexLE [] [])) h)

private theorem k14t7_cover267 : ∀ P ∈ pathPatterns 0 0 [1, 1, 3, 1, 1], HasCheckedCertificate 14 7 ([[], [1, 1, 3, 1, 1]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k14t7p138, Certificates.k14t7p138_check⟩

private theorem k14t7_cover268 : ∀ P ∈ pathPatterns 1 0 [1, 1, 3, 2], HasCheckedCertificate 14 7 ([[], [1, 1, 3, 2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [1, 1, 3, 2] [] ∧ LexLE [] [])) h)

private theorem k14t7_cover269 : ∀ P ∈ pathPatterns 2 1 [1, 1, 4], HasCheckedCertificate 14 7 ([[], [1, 1, 4]] ++ P) := by
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

private theorem k14t7_cover270 : ∀ P ∈ pathPatterns 1 0 [1, 1, 4, 1], HasCheckedCertificate 14 7 ([[], [1, 1, 4, 1]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [1, 1, 4, 1] [] ∧ LexLE [] [])) h)

private theorem k14t7_cover271 : ∀ P ∈ pathPatterns 2 0 [1, 1, 5], HasCheckedCertificate 14 7 ([[], [1, 1, 5]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [1, 1, 5] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k14t7_seq229 : amountSequenceForall 3 5 (fun tail =>
    (LexLE [] ([1, 1] ++ tail) ∧ LexLE ([1, 1] ++ tail) ([1, 1] ++ tail).reverse) →
    ∀ P ∈ pathPatterns (5 - ([1, 1] ++ tail).length) (7 - ([1, 1] ++ tail).sum) ([1, 1] ++ tail),
      HasCheckedCertificate 14 7 ([[]] ++ (([1, 1] ++ tail) :: P))) :=
by
  constructor
  · exact by
      intro _
      exact k14t7_cover230
  · intro q
    fin_cases q
    · exact by
        constructor
        · exact by
            intro _
            exact k14t7_cover241
        · intro q
          fin_cases q
          · exact by
              constructor
              · exact by
                  intro _
                  exact k14t7_cover245
              · intro q
                fin_cases q
                · exact by
                    intro _
                    exact k14t7_cover246
                · exact by
                    intro _
                    exact k14t7_cover247
                · exact by
                    intro _
                    exact k14t7_cover248
          · exact by
              constructor
              · exact by
                  intro _
                  exact k14t7_cover249
              · intro q
                fin_cases q
                · exact by
                    intro _
                    exact k14t7_cover250
                · exact by
                    intro _
                    exact k14t7_cover251
          · exact by
              constructor
              · exact by
                  intro _
                  exact k14t7_cover252
              · intro q
                fin_cases q
                · exact by
                    intro _
                    exact k14t7_cover253
          · exact by
              constructor
              · exact by
                  intro _
                  exact k14t7_cover254
              · intro q
                exact Fin.elim0 q
    · exact by
        constructor
        · exact by
            intro _
            exact k14t7_cover255
        · intro q
          fin_cases q
          · exact by
              constructor
              · exact by
                  intro _
                  exact k14t7_cover258
              · intro q
                fin_cases q
                · exact by
                    intro _
                    exact k14t7_cover259
                · exact by
                    intro _
                    exact k14t7_cover260
          · exact by
              constructor
              · exact by
                  intro _
                  exact k14t7_cover261
              · intro q
                fin_cases q
                · exact by
                    intro _
                    exact k14t7_cover262
          · exact by
              constructor
              · exact by
                  intro _
                  exact k14t7_cover263
              · intro q
                exact Fin.elim0 q
    · exact by
        constructor
        · exact by
            intro _
            exact k14t7_cover264
        · intro q
          fin_cases q
          · exact by
              constructor
              · exact by
                  intro _
                  exact k14t7_cover266
              · intro q
                fin_cases q
                · exact by
                    intro _
                    exact k14t7_cover267
          · exact by
              constructor
              · exact by
                  intro _
                  exact k14t7_cover268
              · intro q
                exact Fin.elim0 q
    · exact by
        constructor
        · exact by
            intro _
            exact k14t7_cover269
        · intro q
          fin_cases q
          · exact by
              constructor
              · exact by
                  intro _
                  exact k14t7_cover270
              · intro q
                exact Fin.elim0 q
    · exact by
        constructor
        · exact by
            intro _
            exact k14t7_cover271
        · intro q
          exact Fin.elim0 q

private theorem k14t7_cover273 : ∀ P ∈ pathPatterns 0 1 [1, 2], HasCheckedCertificate 14 7 ([[], [1, 2], [1, 2]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k14t7p139, Certificates.k14t7p139_check⟩

private theorem k14t7_cover274 : ∀ P ∈ pathPatterns 0 0 [1, 3], HasCheckedCertificate 14 7 ([[], [1, 2], [1, 3]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k14t7p140, Certificates.k14t7p140_check⟩

private theorem k14t7_cover275 : ∀ P ∈ pathPatterns 1 2 [2], HasCheckedCertificate 14 7 ([[], [1, 2], [2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [2] [] ∧ LexLE [] [])) h)

private theorem k14t7_cover276 : ∀ P ∈ pathPatterns 0 0 [2, 2], HasCheckedCertificate 14 7 ([[], [1, 2], [2, 2]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k14t7p141, Certificates.k14t7p141_check⟩

private theorem k14t7_cover277 : ∀ P ∈ pathPatterns 1 1 [3], HasCheckedCertificate 14 7 ([[], [1, 2], [3]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [3] [] ∧ LexLE [] [])) h)

private theorem k14t7_cover278 : ∀ P ∈ pathPatterns 1 0 [4], HasCheckedCertificate 14 7 ([[], [1, 2], [4]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [4] [] ∧ LexLE [] [])) h)

private theorem k14t7_cover272 : ∀ P ∈ pathPatterns 3 4 [1, 2], HasCheckedCertificate 14 7 ([[], [1, 2]] ++ P) := by
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
                  exact k14t7_cover273
              · exact by
                  intro _
                  exact k14t7_cover274
        · exact by
            constructor
            · exact by
                intro _
                exact k14t7_cover275
            · intro q
              fin_cases q
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [1, 2] [2, 1] ∧ LexLE [2, 1] [1, 2])) h)
              · exact by
                  intro _
                  exact k14t7_cover276
        · exact by
            constructor
            · exact by
                intro _
                exact k14t7_cover277
            · intro q
              fin_cases q
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [1, 2] [3, 1] ∧ LexLE [3, 1] [1, 3])) h)
        · exact by
            constructor
            · exact by
                intro _
                exact k14t7_cover278
            · intro q
              exact Fin.elim0 q

private theorem k14t7_cover280 : ∀ P ∈ pathPatterns 0 1 [2], HasCheckedCertificate 14 7 ([[], [1, 2, 1], [2]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k14t7p142, Certificates.k14t7p142_check⟩

private theorem k14t7_cover281 : ∀ P ∈ pathPatterns 0 0 [3], HasCheckedCertificate 14 7 ([[], [1, 2, 1], [3]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k14t7p143, Certificates.k14t7p143_check⟩

private theorem k14t7_cover279 : ∀ P ∈ pathPatterns 2 3 [1, 2, 1], HasCheckedCertificate 14 7 ([[], [1, 2, 1]] ++ P) := by
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
            exact k14t7_cover280
        · exact by
            intro _
            exact k14t7_cover281

private theorem k14t7_cover282 : ∀ P ∈ pathPatterns 0 0 [1, 2, 1, 1, 2], HasCheckedCertificate 14 7 ([[], [1, 2, 1, 1, 2]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k14t7p144, Certificates.k14t7p144_check⟩

private theorem k14t7_cover283 : ∀ P ∈ pathPatterns 1 1 [1, 2, 1, 2], HasCheckedCertificate 14 7 ([[], [1, 2, 1, 2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [1, 2, 1, 2] [] ∧ LexLE [] [])) h)

private theorem k14t7_cover284 : ∀ P ∈ pathPatterns 0 0 [1, 2, 1, 2, 1], HasCheckedCertificate 14 7 ([[], [1, 2, 1, 2, 1]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k14t7p145, Certificates.k14t7p145_check⟩

private theorem k14t7_cover285 : ∀ P ∈ pathPatterns 1 0 [1, 2, 1, 3], HasCheckedCertificate 14 7 ([[], [1, 2, 1, 3]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [1, 2, 1, 3] [] ∧ LexLE [] [])) h)

private theorem k14t7_cover287 : ∀ P ∈ pathPatterns 0 0 [2], HasCheckedCertificate 14 7 ([[], [1, 2, 2], [2]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k14t7p146, Certificates.k14t7p146_check⟩

private theorem k14t7_cover286 : ∀ P ∈ pathPatterns 2 2 [1, 2, 2], HasCheckedCertificate 14 7 ([[], [1, 2, 2]] ++ P) := by
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
            exact k14t7_cover287

private theorem k14t7_cover288 : ∀ P ∈ pathPatterns 1 1 [1, 2, 2, 1], HasCheckedCertificate 14 7 ([[], [1, 2, 2, 1]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [1, 2, 2, 1] [] ∧ LexLE [] [])) h)

private theorem k14t7_cover289 : ∀ P ∈ pathPatterns 1 0 [1, 2, 2, 2], HasCheckedCertificate 14 7 ([[], [1, 2, 2, 2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [1, 2, 2, 2] [] ∧ LexLE [] [])) h)

private theorem k14t7_cover290 : ∀ P ∈ pathPatterns 2 1 [1, 2, 3], HasCheckedCertificate 14 7 ([[], [1, 2, 3]] ++ P) := by
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

private theorem k14t7_cover291 : ∀ P ∈ pathPatterns 1 0 [1, 2, 3, 1], HasCheckedCertificate 14 7 ([[], [1, 2, 3, 1]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [1, 2, 3, 1] [] ∧ LexLE [] [])) h)

private theorem k14t7_cover292 : ∀ P ∈ pathPatterns 2 0 [1, 2, 4], HasCheckedCertificate 14 7 ([[], [1, 2, 4]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [1, 2, 4] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k14t7_cover294 : ∀ P ∈ pathPatterns 1 1 [2], HasCheckedCertificate 14 7 ([[], [1, 3], [2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [2] [] ∧ LexLE [] [])) h)

private theorem k14t7_cover295 : ∀ P ∈ pathPatterns 1 0 [3], HasCheckedCertificate 14 7 ([[], [1, 3], [3]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [3] [] ∧ LexLE [] [])) h)

private theorem k14t7_cover293 : ∀ P ∈ pathPatterns 3 3 [1, 3], HasCheckedCertificate 14 7 ([[], [1, 3]] ++ P) := by
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
                exact k14t7_cover294
            · intro q
              fin_cases q
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [1, 3] [2, 1] ∧ LexLE [2, 1] [1, 2])) h)
        · exact by
            constructor
            · exact by
                intro _
                exact k14t7_cover295
            · intro q
              exact Fin.elim0 q

private theorem k14t7_cover297 : ∀ P ∈ pathPatterns 0 0 [2], HasCheckedCertificate 14 7 ([[], [1, 3, 1], [2]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k14t7p147, Certificates.k14t7p147_check⟩

private theorem k14t7_cover296 : ∀ P ∈ pathPatterns 2 2 [1, 3, 1], HasCheckedCertificate 14 7 ([[], [1, 3, 1]] ++ P) := by
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
            exact k14t7_cover297

private theorem k14t7_cover298 : ∀ P ∈ pathPatterns 1 0 [1, 3, 1, 2], HasCheckedCertificate 14 7 ([[], [1, 3, 1, 2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [1, 3, 1, 2] [] ∧ LexLE [] [])) h)

private theorem k14t7_cover299 : ∀ P ∈ pathPatterns 2 1 [1, 3, 2], HasCheckedCertificate 14 7 ([[], [1, 3, 2]] ++ P) := by
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

private theorem k14t7_cover300 : ∀ P ∈ pathPatterns 2 0 [1, 3, 3], HasCheckedCertificate 14 7 ([[], [1, 3, 3]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [1, 3, 3] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k14t7_cover302 : ∀ P ∈ pathPatterns 1 0 [2], HasCheckedCertificate 14 7 ([[], [1, 4], [2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [2] [] ∧ LexLE [] [])) h)

private theorem k14t7_cover301 : ∀ P ∈ pathPatterns 3 2 [1, 4], HasCheckedCertificate 14 7 ([[], [1, 4]] ++ P) := by
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
                exact k14t7_cover302
            · intro q
              exact Fin.elim0 q

private theorem k14t7_cover303 : ∀ P ∈ pathPatterns 2 1 [1, 4, 1], HasCheckedCertificate 14 7 ([[], [1, 4, 1]] ++ P) := by
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

private theorem k14t7_cover304 : ∀ P ∈ pathPatterns 2 0 [1, 4, 2], HasCheckedCertificate 14 7 ([[], [1, 4, 2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [1, 4, 2] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k14t7_cover305 : ∀ P ∈ pathPatterns 3 1 [1, 5], HasCheckedCertificate 14 7 ([[], [1, 5]] ++ P) := by
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

private theorem k14t7_cover306 : ∀ P ∈ pathPatterns 2 0 [1, 5, 1], HasCheckedCertificate 14 7 ([[], [1, 5, 1]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [1, 5, 1] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k14t7_cover307 : ∀ P ∈ pathPatterns 3 0 [1, 6], HasCheckedCertificate 14 7 ([[], [1, 6]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [1, 6] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k14t7_seq189 : amountSequenceForall 4 6 (fun tail =>
    (LexLE [] ([1] ++ tail) ∧ LexLE ([1] ++ tail) ([1] ++ tail).reverse) →
    ∀ P ∈ pathPatterns (5 - ([1] ++ tail).length) (7 - ([1] ++ tail).sum) ([1] ++ tail),
      HasCheckedCertificate 14 7 ([[]] ++ (([1] ++ tail) :: P))) :=
by
  constructor
  · exact by
      intro _
      exact k14t7_cover190
  · intro q
    fin_cases q
    · exact k14t7_seq229

    · exact by
        constructor
        · exact by
            intro _
            exact k14t7_cover272
        · intro q
          fin_cases q
          · exact by
              constructor
              · exact by
                  intro _
                  exact k14t7_cover279
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
                          exact k14t7_cover282
                · exact by
                    constructor
                    · exact by
                        intro _
                        exact k14t7_cover283
                    · intro q
                      fin_cases q
                      · exact by
                          intro _
                          exact k14t7_cover284
                · exact by
                    constructor
                    · exact by
                        intro _
                        exact k14t7_cover285
                    · intro q
                      exact Fin.elim0 q
          · exact by
              constructor
              · exact by
                  intro _
                  exact k14t7_cover286
              · intro q
                fin_cases q
                · exact by
                    constructor
                    · exact by
                        intro _
                        exact k14t7_cover288
                    · intro q
                      fin_cases q
                      · exact by
                          intro h
                          exact False.elim ((by decide : ¬ (LexLE [] [1, 2, 2, 1, 1] ∧ LexLE [1, 2, 2, 1, 1] [1, 1, 2, 2, 1])) h)
                · exact by
                    constructor
                    · exact by
                        intro _
                        exact k14t7_cover289
                    · intro q
                      exact Fin.elim0 q
          · exact by
              constructor
              · exact by
                  intro _
                  exact k14t7_cover290
              · intro q
                fin_cases q
                · exact by
                    constructor
                    · exact by
                        intro _
                        exact k14t7_cover291
                    · intro q
                      exact Fin.elim0 q
          · exact by
              constructor
              · exact by
                  intro _
                  exact k14t7_cover292
              · intro q
                exact Fin.elim0 q
    · exact by
        constructor
        · exact by
            intro _
            exact k14t7_cover293
        · intro q
          fin_cases q
          · exact by
              constructor
              · exact by
                  intro _
                  exact k14t7_cover296
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
                    constructor
                    · exact by
                        intro _
                        exact k14t7_cover298
                    · intro q
                      exact Fin.elim0 q
          · exact by
              constructor
              · exact by
                  intro _
                  exact k14t7_cover299
              · intro q
                fin_cases q
                · exact by
                    constructor
                    · exact by
                        intro h
                        exact False.elim ((by decide : ¬ (LexLE [] [1, 3, 2, 1] ∧ LexLE [1, 3, 2, 1] [1, 2, 3, 1])) h)
                    · intro q
                      exact Fin.elim0 q
          · exact by
              constructor
              · exact by
                  intro _
                  exact k14t7_cover300
              · intro q
                exact Fin.elim0 q
    · exact by
        constructor
        · exact by
            intro _
            exact k14t7_cover301
        · intro q
          fin_cases q
          · exact by
              constructor
              · exact by
                  intro _
                  exact k14t7_cover303
              · intro q
                fin_cases q
                · exact by
                    constructor
                    · exact by
                        intro h
                        exact False.elim ((by decide : ¬ (LexLE [] [1, 4, 1, 1] ∧ LexLE [1, 4, 1, 1] [1, 1, 4, 1])) h)
                    · intro q
                      exact Fin.elim0 q
          · exact by
              constructor
              · exact by
                  intro _
                  exact k14t7_cover304
              · intro q
                exact Fin.elim0 q
    · exact by
        constructor
        · exact by
            intro _
            exact k14t7_cover305
        · intro q
          fin_cases q
          · exact by
              constructor
              · exact by
                  intro _
                  exact k14t7_cover306
              · intro q
                exact Fin.elim0 q
    · exact by
        constructor
        · exact by
            intro _
            exact k14t7_cover307
        · intro q
          exact Fin.elim0 q

private theorem k14t7_cover312 : ∀ P ∈ pathPatterns 0 1 [2], HasCheckedCertificate 14 7 ([[], [2], [2], [2]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k14t7p148, Certificates.k14t7p148_check⟩

private theorem k14t7_cover313 : ∀ P ∈ pathPatterns 0 0 [3], HasCheckedCertificate 14 7 ([[], [2], [2], [3]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k14t7p149, Certificates.k14t7p149_check⟩

private theorem k14t7_cover311 : ∀ P ∈ pathPatterns 2 3 [2], HasCheckedCertificate 14 7 ([[], [2], [2]] ++ P) := by
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
            exact k14t7_cover312
        · exact by
            intro _
            exact k14t7_cover313

private theorem k14t7_cover314 : ∀ P ∈ pathPatterns 0 0 [2, 1, 2], HasCheckedCertificate 14 7 ([[], [2], [2, 1, 2]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k14t7p150, Certificates.k14t7p150_check⟩

private theorem k14t7_cover315 : ∀ P ∈ pathPatterns 1 1 [2, 2], HasCheckedCertificate 14 7 ([[], [2], [2, 2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [2, 2] [] ∧ LexLE [] [])) h)

private theorem k14t7_cover316 : ∀ P ∈ pathPatterns 1 0 [2, 3], HasCheckedCertificate 14 7 ([[], [2], [2, 3]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [2, 3] [] ∧ LexLE [] [])) h)

private theorem k14t7_cover317 : ∀ P ∈ pathPatterns 2 2 [3], HasCheckedCertificate 14 7 ([[], [2], [3]] ++ P) := by
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

private theorem k14t7_cover318 : ∀ P ∈ pathPatterns 2 1 [4], HasCheckedCertificate 14 7 ([[], [2], [4]] ++ P) := by
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

private theorem k14t7_cover319 : ∀ P ∈ pathPatterns 2 0 [5], HasCheckedCertificate 14 7 ([[], [2], [5]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [5] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k14t7_seq310 : amountSequenceForall 3 5 (fun tail =>
    (LexLE [2] ([] ++ tail) ∧ LexLE ([] ++ tail) ([] ++ tail).reverse) →
    ∀ P ∈ pathPatterns (3 - ([] ++ tail).length) (5 - ([] ++ tail).sum) ([] ++ tail),
      HasCheckedCertificate 14 7 ([[], [2]] ++ (([] ++ tail) :: P))) :=
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
            exact k14t7_cover311
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
                    exact k14t7_cover314
          · exact by
              constructor
              · exact by
                  intro _
                  exact k14t7_cover315
              · intro q
                fin_cases q
                · exact by
                    intro h
                    exact False.elim ((by decide : ¬ (LexLE [2] [2, 2, 1] ∧ LexLE [2, 2, 1] [1, 2, 2])) h)
          · exact by
              constructor
              · exact by
                  intro _
                  exact k14t7_cover316
              · intro q
                exact Fin.elim0 q
    · exact by
        constructor
        · exact by
            intro _
            exact k14t7_cover317
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
            exact k14t7_cover318
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
            exact k14t7_cover319
        · intro q
          exact Fin.elim0 q

private theorem k14t7_cover309 : ∀ P ∈ pathPatterns 4 5 [2], HasCheckedCertificate 14 7 ([[], [2]] ++ P) := by
  apply pathPatterns_forall_step
  exact k14t7_seq310


private theorem k14t7_cover320 : ∀ P ∈ pathPatterns 0 0 [2, 1, 1, 1, 2], HasCheckedCertificate 14 7 ([[], [2, 1, 1, 1, 2]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k14t7p151, Certificates.k14t7p151_check⟩

private theorem k14t7_cover321 : ∀ P ∈ pathPatterns 1 1 [2, 1, 1, 2], HasCheckedCertificate 14 7 ([[], [2, 1, 1, 2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [2, 1, 1, 2] [] ∧ LexLE [] [])) h)

private theorem k14t7_cover322 : ∀ P ∈ pathPatterns 1 0 [2, 1, 1, 3], HasCheckedCertificate 14 7 ([[], [2, 1, 1, 3]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [2, 1, 1, 3] [] ∧ LexLE [] [])) h)

private theorem k14t7_cover323 : ∀ P ∈ pathPatterns 2 2 [2, 1, 2], HasCheckedCertificate 14 7 ([[], [2, 1, 2]] ++ P) := by
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

private theorem k14t7_cover324 : ∀ P ∈ pathPatterns 1 0 [2, 1, 2, 2], HasCheckedCertificate 14 7 ([[], [2, 1, 2, 2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [2, 1, 2, 2] [] ∧ LexLE [] [])) h)

private theorem k14t7_cover325 : ∀ P ∈ pathPatterns 2 1 [2, 1, 3], HasCheckedCertificate 14 7 ([[], [2, 1, 3]] ++ P) := by
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

private theorem k14t7_cover326 : ∀ P ∈ pathPatterns 2 0 [2, 1, 4], HasCheckedCertificate 14 7 ([[], [2, 1, 4]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [2, 1, 4] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k14t7_cover328 : ∀ P ∈ pathPatterns 1 0 [3], HasCheckedCertificate 14 7 ([[], [2, 2], [3]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [3] [] ∧ LexLE [] [])) h)

private theorem k14t7_cover327 : ∀ P ∈ pathPatterns 3 3 [2, 2], HasCheckedCertificate 14 7 ([[], [2, 2]] ++ P) := by
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
                exact k14t7_cover328
            · intro q
              exact Fin.elim0 q

private theorem k14t7_cover329 : ∀ P ∈ pathPatterns 2 1 [2, 2, 2], HasCheckedCertificate 14 7 ([[], [2, 2, 2]] ++ P) := by
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

private theorem k14t7_cover330 : ∀ P ∈ pathPatterns 2 0 [2, 2, 3], HasCheckedCertificate 14 7 ([[], [2, 2, 3]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [2, 2, 3] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k14t7_cover331 : ∀ P ∈ pathPatterns 3 2 [2, 3], HasCheckedCertificate 14 7 ([[], [2, 3]] ++ P) := by
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

private theorem k14t7_cover332 : ∀ P ∈ pathPatterns 2 0 [2, 3, 2], HasCheckedCertificate 14 7 ([[], [2, 3, 2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [2, 3, 2] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k14t7_cover333 : ∀ P ∈ pathPatterns 3 1 [2, 4], HasCheckedCertificate 14 7 ([[], [2, 4]] ++ P) := by
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

private theorem k14t7_cover334 : ∀ P ∈ pathPatterns 3 0 [2, 5], HasCheckedCertificate 14 7 ([[], [2, 5]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [2, 5] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k14t7_seq308 : amountSequenceForall 4 5 (fun tail =>
    (LexLE [] ([2] ++ tail) ∧ LexLE ([2] ++ tail) ([2] ++ tail).reverse) →
    ∀ P ∈ pathPatterns (5 - ([2] ++ tail).length) (7 - ([2] ++ tail).sum) ([2] ++ tail),
      HasCheckedCertificate 14 7 ([[]] ++ (([2] ++ tail) :: P))) :=
by
  constructor
  · exact by
      intro _
      exact k14t7_cover309
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
                          exact k14t7_cover320
                · exact by
                    constructor
                    · exact by
                        intro _
                        exact k14t7_cover321
                    · intro q
                      fin_cases q
                      · exact by
                          intro h
                          exact False.elim ((by decide : ¬ (LexLE [] [2, 1, 1, 2, 1] ∧ LexLE [2, 1, 1, 2, 1] [1, 2, 1, 1, 2])) h)
                · exact by
                    constructor
                    · exact by
                        intro _
                        exact k14t7_cover322
                    · intro q
                      exact Fin.elim0 q
          · exact by
              constructor
              · exact by
                  intro _
                  exact k14t7_cover323
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
                    constructor
                    · exact by
                        intro _
                        exact k14t7_cover324
                    · intro q
                      exact Fin.elim0 q
          · exact by
              constructor
              · exact by
                  intro _
                  exact k14t7_cover325
              · intro q
                fin_cases q
                · exact by
                    constructor
                    · exact by
                        intro h
                        exact False.elim ((by decide : ¬ (LexLE [] [2, 1, 3, 1] ∧ LexLE [2, 1, 3, 1] [1, 3, 1, 2])) h)
                    · intro q
                      exact Fin.elim0 q
          · exact by
              constructor
              · exact by
                  intro _
                  exact k14t7_cover326
              · intro q
                exact Fin.elim0 q
    · exact by
        constructor
        · exact by
            intro _
            exact k14t7_cover327
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
                    constructor
                    · exact by
                        intro h
                        exact False.elim ((by decide : ¬ (LexLE [] [2, 2, 1, 2] ∧ LexLE [2, 2, 1, 2] [2, 1, 2, 2])) h)
                    · intro q
                      exact Fin.elim0 q
          · exact by
              constructor
              · exact by
                  intro _
                  exact k14t7_cover329
              · intro q
                fin_cases q
                · exact by
                    constructor
                    · exact by
                        intro h
                        exact False.elim ((by decide : ¬ (LexLE [] [2, 2, 2, 1] ∧ LexLE [2, 2, 2, 1] [1, 2, 2, 2])) h)
                    · intro q
                      exact Fin.elim0 q
          · exact by
              constructor
              · exact by
                  intro _
                  exact k14t7_cover330
              · intro q
                exact Fin.elim0 q
    · exact by
        constructor
        · exact by
            intro _
            exact k14t7_cover331
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
                      exact Fin.elim0 q
          · exact by
              constructor
              · exact by
                  intro _
                  exact k14t7_cover332
              · intro q
                exact Fin.elim0 q
    · exact by
        constructor
        · exact by
            intro _
            exact k14t7_cover333
        · intro q
          fin_cases q
          · exact by
              constructor
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [] [2, 4, 1] ∧ LexLE [2, 4, 1] [1, 4, 2])) h)
              · intro q
                exact Fin.elim0 q
    · exact by
        constructor
        · exact by
            intro _
            exact k14t7_cover334
        · intro q
          exact Fin.elim0 q

private theorem k14t7_cover336 : ∀ P ∈ pathPatterns 2 1 [3], HasCheckedCertificate 14 7 ([[], [3], [3]] ++ P) := by
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

private theorem k14t7_cover337 : ∀ P ∈ pathPatterns 2 0 [4], HasCheckedCertificate 14 7 ([[], [3], [4]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [4] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k14t7_cover335 : ∀ P ∈ pathPatterns 4 4 [3], HasCheckedCertificate 14 7 ([[], [3]] ++ P) := by
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
                exact k14t7_cover336
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
                exact k14t7_cover337
            · intro q
              exact Fin.elim0 q

private theorem k14t7_cover338 : ∀ P ∈ pathPatterns 2 0 [3, 1, 3], HasCheckedCertificate 14 7 ([[], [3, 1, 3]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [3, 1, 3] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k14t7_cover339 : ∀ P ∈ pathPatterns 3 1 [3, 3], HasCheckedCertificate 14 7 ([[], [3, 3]] ++ P) := by
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

private theorem k14t7_cover340 : ∀ P ∈ pathPatterns 3 0 [3, 4], HasCheckedCertificate 14 7 ([[], [3, 4]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [3, 4] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k14t7_cover341 : ∀ P ∈ pathPatterns 4 3 [4], HasCheckedCertificate 14 7 ([[], [4]] ++ P) := by
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

private theorem k14t7_cover342 : ∀ P ∈ pathPatterns 4 2 [5], HasCheckedCertificate 14 7 ([[], [5]] ++ P) := by
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

private theorem k14t7_cover343 : ∀ P ∈ pathPatterns 4 1 [6], HasCheckedCertificate 14 7 ([[], [6]] ++ P) := by
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

private theorem k14t7_cover344 : ∀ P ∈ pathPatterns 4 0 [7], HasCheckedCertificate 14 7 ([[], [7]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [7] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k14t7_seq4 : amountSequenceForall 5 7 (fun tail =>
    (LexLE [] ([] ++ tail) ∧ LexLE ([] ++ tail) ([] ++ tail).reverse) →
    ∀ P ∈ pathPatterns (5 - ([] ++ tail).length) (7 - ([] ++ tail).sum) ([] ++ tail),
      HasCheckedCertificate 14 7 ([[]] ++ (([] ++ tail) :: P))) :=
by
  constructor
  · exact by
      intro _
      exact k14t7_cover5
  · intro q
    fin_cases q
    · exact k14t7_seq189

    · exact k14t7_seq308

    · exact by
        constructor
        · exact by
            intro _
            exact k14t7_cover335
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
                          constructor
                          · exact by
                              intro h
                              exact False.elim ((by decide : ¬ (LexLE [] [3, 1, 1, 2] ∧ LexLE [3, 1, 1, 2] [2, 1, 1, 3])) h)
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
                            exact Fin.elim0 q
                · exact by
                    constructor
                    · exact by
                        intro _
                        exact k14t7_cover338
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
                            exact Fin.elim0 q
                · exact by
                    constructor
                    · exact by
                        intro h
                        exact False.elim ((by decide : ¬ (LexLE [] [3, 2, 2] ∧ LexLE [3, 2, 2] [2, 2, 3])) h)
                    · intro q
                      exact Fin.elim0 q
          · exact by
              constructor
              · exact by
                  intro _
                  exact k14t7_cover339
              · intro q
                fin_cases q
                · exact by
                    constructor
                    · exact by
                        intro h
                        exact False.elim ((by decide : ¬ (LexLE [] [3, 3, 1] ∧ LexLE [3, 3, 1] [1, 3, 3])) h)
                    · intro q
                      exact Fin.elim0 q
          · exact by
              constructor
              · exact by
                  intro _
                  exact k14t7_cover340
              · intro q
                exact Fin.elim0 q
    · exact by
        constructor
        · exact by
            intro _
            exact k14t7_cover341
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
                            exact Fin.elim0 q
                · exact by
                    constructor
                    · exact by
                        intro h
                        exact False.elim ((by decide : ¬ (LexLE [] [4, 1, 2] ∧ LexLE [4, 1, 2] [2, 1, 4])) h)
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
                      exact Fin.elim0 q
          · exact by
              constructor
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [] [4, 3] ∧ LexLE [4, 3] [3, 4])) h)
              · intro q
                exact Fin.elim0 q
    · exact by
        constructor
        · exact by
            intro _
            exact k14t7_cover342
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
                      exact Fin.elim0 q
          · exact by
              constructor
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [] [5, 2] ∧ LexLE [5, 2] [2, 5])) h)
              · intro q
                exact Fin.elim0 q
    · exact by
        constructor
        · exact by
            intro _
            exact k14t7_cover343
        · intro q
          fin_cases q
          · exact by
              constructor
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [] [6, 1] ∧ LexLE [6, 1] [1, 6])) h)
              · intro q
                exact Fin.elim0 q
    · exact by
        constructor
        · exact by
            intro _
            exact k14t7_cover344
        · intro q
          exact Fin.elim0 q

private theorem k14t7_cover3 : ∀ P ∈ pathPatterns 6 7 [], HasCheckedCertificate 14 7 ([[]] ++ P) := by
  apply pathPatterns_forall_step
  exact k14t7_seq4


private theorem k14t7_cover350 : ∀ P ∈ pathPatterns 1 4 [1], HasCheckedCertificate 14 7 ([[1], [1], [1]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [1] [] ∧ LexLE [] [])) h)

private theorem k14t7_cover351 : ∀ P ∈ pathPatterns 0 3 [1, 1], HasCheckedCertificate 14 7 ([[1], [1], [1, 1]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k14t7p152, Certificates.k14t7p152_check⟩

private theorem k14t7_cover352 : ∀ P ∈ pathPatterns 0 2 [1, 2], HasCheckedCertificate 14 7 ([[1], [1], [1, 2]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k14t7p153, Certificates.k14t7p153_check⟩

private theorem k14t7_cover353 : ∀ P ∈ pathPatterns 0 1 [1, 3], HasCheckedCertificate 14 7 ([[1], [1], [1, 3]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k14t7p154, Certificates.k14t7p154_check⟩

private theorem k14t7_cover354 : ∀ P ∈ pathPatterns 0 0 [1, 4], HasCheckedCertificate 14 7 ([[1], [1], [1, 4]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k14t7p155, Certificates.k14t7p155_check⟩

private theorem k14t7_cover355 : ∀ P ∈ pathPatterns 1 3 [2], HasCheckedCertificate 14 7 ([[1], [1], [2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [2] [] ∧ LexLE [] [])) h)

private theorem k14t7_cover356 : ∀ P ∈ pathPatterns 0 1 [2, 2], HasCheckedCertificate 14 7 ([[1], [1], [2, 2]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k14t7p156, Certificates.k14t7p156_check⟩

private theorem k14t7_cover357 : ∀ P ∈ pathPatterns 0 0 [2, 3], HasCheckedCertificate 14 7 ([[1], [1], [2, 3]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k14t7p157, Certificates.k14t7p157_check⟩

private theorem k14t7_cover358 : ∀ P ∈ pathPatterns 1 2 [3], HasCheckedCertificate 14 7 ([[1], [1], [3]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [3] [] ∧ LexLE [] [])) h)

private theorem k14t7_cover359 : ∀ P ∈ pathPatterns 1 1 [4], HasCheckedCertificate 14 7 ([[1], [1], [4]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [4] [] ∧ LexLE [] [])) h)

private theorem k14t7_cover360 : ∀ P ∈ pathPatterns 1 0 [5], HasCheckedCertificate 14 7 ([[1], [1], [5]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [5] [] ∧ LexLE [] [])) h)

private theorem k14t7_cover349 : ∀ P ∈ pathPatterns 3 5 [1], HasCheckedCertificate 14 7 ([[1], [1]] ++ P) := by
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
                exact k14t7_cover350
            · intro q
              fin_cases q
              · exact by
                  intro _
                  exact k14t7_cover351
              · exact by
                  intro _
                  exact k14t7_cover352
              · exact by
                  intro _
                  exact k14t7_cover353
              · exact by
                  intro _
                  exact k14t7_cover354
        · exact by
            constructor
            · exact by
                intro _
                exact k14t7_cover355
            · intro q
              fin_cases q
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [1] [2, 1] ∧ LexLE [2, 1] [1, 2])) h)
              · exact by
                  intro _
                  exact k14t7_cover356
              · exact by
                  intro _
                  exact k14t7_cover357
        · exact by
            constructor
            · exact by
                intro _
                exact k14t7_cover358
            · intro q
              fin_cases q
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [1] [3, 1] ∧ LexLE [3, 1] [1, 3])) h)
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [1] [3, 2] ∧ LexLE [3, 2] [2, 3])) h)
        · exact by
            constructor
            · exact by
                intro _
                exact k14t7_cover359
            · intro q
              fin_cases q
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [1] [4, 1] ∧ LexLE [4, 1] [1, 4])) h)
        · exact by
            constructor
            · exact by
                intro _
                exact k14t7_cover360
            · intro q
              exact Fin.elim0 q

private theorem k14t7_cover362 : ∀ P ∈ pathPatterns 0 2 [2], HasCheckedCertificate 14 7 ([[1], [1, 1], [2]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k14t7p158, Certificates.k14t7p158_check⟩

private theorem k14t7_cover363 : ∀ P ∈ pathPatterns 0 1 [3], HasCheckedCertificate 14 7 ([[1], [1, 1], [3]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k14t7p159, Certificates.k14t7p159_check⟩

private theorem k14t7_cover364 : ∀ P ∈ pathPatterns 0 0 [4], HasCheckedCertificate 14 7 ([[1], [1, 1], [4]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k14t7p160, Certificates.k14t7p160_check⟩

private theorem k14t7_cover361 : ∀ P ∈ pathPatterns 2 4 [1, 1], HasCheckedCertificate 14 7 ([[1], [1, 1]] ++ P) := by
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
            exact k14t7_cover362
        · exact by
            intro _
            exact k14t7_cover363
        · exact by
            intro _
            exact k14t7_cover364

private theorem k14t7_cover365 : ∀ P ∈ pathPatterns 1 3 [1, 1, 1], HasCheckedCertificate 14 7 ([[1], [1, 1, 1]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [1, 1, 1] [] ∧ LexLE [] [])) h)

private theorem k14t7_cover366 : ∀ P ∈ pathPatterns 0 2 [1, 1, 1, 1], HasCheckedCertificate 14 7 ([[1], [1, 1, 1, 1]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k14t7p161, Certificates.k14t7p161_check⟩

private theorem k14t7_cover367 : ∀ P ∈ pathPatterns 0 1 [1, 1, 1, 2], HasCheckedCertificate 14 7 ([[1], [1, 1, 1, 2]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k14t7p162, Certificates.k14t7p162_check⟩

private theorem k14t7_cover368 : ∀ P ∈ pathPatterns 0 0 [1, 1, 1, 3], HasCheckedCertificate 14 7 ([[1], [1, 1, 1, 3]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k14t7p163, Certificates.k14t7p163_check⟩

private theorem k14t7_cover369 : ∀ P ∈ pathPatterns 1 2 [1, 1, 2], HasCheckedCertificate 14 7 ([[1], [1, 1, 2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [1, 1, 2] [] ∧ LexLE [] [])) h)

private theorem k14t7_cover370 : ∀ P ∈ pathPatterns 0 1 [1, 1, 2, 1], HasCheckedCertificate 14 7 ([[1], [1, 1, 2, 1]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k14t7p164, Certificates.k14t7p164_check⟩

private theorem k14t7_cover371 : ∀ P ∈ pathPatterns 0 0 [1, 1, 2, 2], HasCheckedCertificate 14 7 ([[1], [1, 1, 2, 2]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k14t7p165, Certificates.k14t7p165_check⟩

private theorem k14t7_cover372 : ∀ P ∈ pathPatterns 1 1 [1, 1, 3], HasCheckedCertificate 14 7 ([[1], [1, 1, 3]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [1, 1, 3] [] ∧ LexLE [] [])) h)

private theorem k14t7_cover373 : ∀ P ∈ pathPatterns 0 0 [1, 1, 3, 1], HasCheckedCertificate 14 7 ([[1], [1, 1, 3, 1]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k14t7p166, Certificates.k14t7p166_check⟩

private theorem k14t7_cover374 : ∀ P ∈ pathPatterns 1 0 [1, 1, 4], HasCheckedCertificate 14 7 ([[1], [1, 1, 4]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [1, 1, 4] [] ∧ LexLE [] [])) h)

private theorem k14t7_cover376 : ∀ P ∈ pathPatterns 0 1 [2], HasCheckedCertificate 14 7 ([[1], [1, 2], [2]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k14t7p167, Certificates.k14t7p167_check⟩

private theorem k14t7_cover377 : ∀ P ∈ pathPatterns 0 0 [3], HasCheckedCertificate 14 7 ([[1], [1, 2], [3]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k14t7p168, Certificates.k14t7p168_check⟩

private theorem k14t7_cover375 : ∀ P ∈ pathPatterns 2 3 [1, 2], HasCheckedCertificate 14 7 ([[1], [1, 2]] ++ P) := by
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
            exact k14t7_cover376
        · exact by
            intro _
            exact k14t7_cover377

private theorem k14t7_cover378 : ∀ P ∈ pathPatterns 1 2 [1, 2, 1], HasCheckedCertificate 14 7 ([[1], [1, 2, 1]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [1, 2, 1] [] ∧ LexLE [] [])) h)

private theorem k14t7_cover379 : ∀ P ∈ pathPatterns 0 0 [1, 2, 1, 2], HasCheckedCertificate 14 7 ([[1], [1, 2, 1, 2]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k14t7p169, Certificates.k14t7p169_check⟩

private theorem k14t7_cover380 : ∀ P ∈ pathPatterns 1 1 [1, 2, 2], HasCheckedCertificate 14 7 ([[1], [1, 2, 2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [1, 2, 2] [] ∧ LexLE [] [])) h)

private theorem k14t7_cover381 : ∀ P ∈ pathPatterns 0 0 [1, 2, 2, 1], HasCheckedCertificate 14 7 ([[1], [1, 2, 2, 1]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k14t7p170, Certificates.k14t7p170_check⟩

private theorem k14t7_cover382 : ∀ P ∈ pathPatterns 1 0 [1, 2, 3], HasCheckedCertificate 14 7 ([[1], [1, 2, 3]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [1, 2, 3] [] ∧ LexLE [] [])) h)

private theorem k14t7_cover384 : ∀ P ∈ pathPatterns 0 0 [2], HasCheckedCertificate 14 7 ([[1], [1, 3], [2]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k14t7p171, Certificates.k14t7p171_check⟩

private theorem k14t7_cover383 : ∀ P ∈ pathPatterns 2 2 [1, 3], HasCheckedCertificate 14 7 ([[1], [1, 3]] ++ P) := by
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
            exact k14t7_cover384

private theorem k14t7_cover385 : ∀ P ∈ pathPatterns 1 1 [1, 3, 1], HasCheckedCertificate 14 7 ([[1], [1, 3, 1]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [1, 3, 1] [] ∧ LexLE [] [])) h)

private theorem k14t7_cover386 : ∀ P ∈ pathPatterns 1 0 [1, 3, 2], HasCheckedCertificate 14 7 ([[1], [1, 3, 2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [1, 3, 2] [] ∧ LexLE [] [])) h)

private theorem k14t7_cover387 : ∀ P ∈ pathPatterns 2 1 [1, 4], HasCheckedCertificate 14 7 ([[1], [1, 4]] ++ P) := by
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

private theorem k14t7_cover388 : ∀ P ∈ pathPatterns 1 0 [1, 4, 1], HasCheckedCertificate 14 7 ([[1], [1, 4, 1]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [1, 4, 1] [] ∧ LexLE [] [])) h)

private theorem k14t7_cover389 : ∀ P ∈ pathPatterns 2 0 [1, 5], HasCheckedCertificate 14 7 ([[1], [1, 5]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [1, 5] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k14t7_seq348 : amountSequenceForall 3 5 (fun tail =>
    (LexLE [1] ([1] ++ tail) ∧ LexLE ([1] ++ tail) ([1] ++ tail).reverse) →
    ∀ P ∈ pathPatterns (4 - ([1] ++ tail).length) (6 - ([1] ++ tail).sum) ([1] ++ tail),
      HasCheckedCertificate 14 7 ([[1]] ++ (([1] ++ tail) :: P))) :=
by
  constructor
  · exact by
      intro _
      exact k14t7_cover349
  · intro q
    fin_cases q
    · exact by
        constructor
        · exact by
            intro _
            exact k14t7_cover361
        · intro q
          fin_cases q
          · exact by
              constructor
              · exact by
                  intro _
                  exact k14t7_cover365
              · intro q
                fin_cases q
                · exact by
                    intro _
                    exact k14t7_cover366
                · exact by
                    intro _
                    exact k14t7_cover367
                · exact by
                    intro _
                    exact k14t7_cover368
          · exact by
              constructor
              · exact by
                  intro _
                  exact k14t7_cover369
              · intro q
                fin_cases q
                · exact by
                    intro _
                    exact k14t7_cover370
                · exact by
                    intro _
                    exact k14t7_cover371
          · exact by
              constructor
              · exact by
                  intro _
                  exact k14t7_cover372
              · intro q
                fin_cases q
                · exact by
                    intro _
                    exact k14t7_cover373
          · exact by
              constructor
              · exact by
                  intro _
                  exact k14t7_cover374
              · intro q
                exact Fin.elim0 q
    · exact by
        constructor
        · exact by
            intro _
            exact k14t7_cover375
        · intro q
          fin_cases q
          · exact by
              constructor
              · exact by
                  intro _
                  exact k14t7_cover378
              · intro q
                fin_cases q
                · exact by
                    intro h
                    exact False.elim ((by decide : ¬ (LexLE [1] [1, 2, 1, 1] ∧ LexLE [1, 2, 1, 1] [1, 1, 2, 1])) h)
                · exact by
                    intro _
                    exact k14t7_cover379
          · exact by
              constructor
              · exact by
                  intro _
                  exact k14t7_cover380
              · intro q
                fin_cases q
                · exact by
                    intro _
                    exact k14t7_cover381
          · exact by
              constructor
              · exact by
                  intro _
                  exact k14t7_cover382
              · intro q
                exact Fin.elim0 q
    · exact by
        constructor
        · exact by
            intro _
            exact k14t7_cover383
        · intro q
          fin_cases q
          · exact by
              constructor
              · exact by
                  intro _
                  exact k14t7_cover385
              · intro q
                fin_cases q
                · exact by
                    intro h
                    exact False.elim ((by decide : ¬ (LexLE [1] [1, 3, 1, 1] ∧ LexLE [1, 3, 1, 1] [1, 1, 3, 1])) h)
          · exact by
              constructor
              · exact by
                  intro _
                  exact k14t7_cover386
              · intro q
                exact Fin.elim0 q
    · exact by
        constructor
        · exact by
            intro _
            exact k14t7_cover387
        · intro q
          fin_cases q
          · exact by
              constructor
              · exact by
                  intro _
                  exact k14t7_cover388
              · intro q
                exact Fin.elim0 q
    · exact by
        constructor
        · exact by
            intro _
            exact k14t7_cover389
        · intro q
          exact Fin.elim0 q

private theorem k14t7_cover391 : ∀ P ∈ pathPatterns 1 2 [2], HasCheckedCertificate 14 7 ([[1], [2], [2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [2] [] ∧ LexLE [] [])) h)

private theorem k14t7_cover392 : ∀ P ∈ pathPatterns 0 0 [2, 2], HasCheckedCertificate 14 7 ([[1], [2], [2, 2]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k14t7p172, Certificates.k14t7p172_check⟩

private theorem k14t7_cover393 : ∀ P ∈ pathPatterns 1 1 [3], HasCheckedCertificate 14 7 ([[1], [2], [3]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [3] [] ∧ LexLE [] [])) h)

private theorem k14t7_cover394 : ∀ P ∈ pathPatterns 1 0 [4], HasCheckedCertificate 14 7 ([[1], [2], [4]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [4] [] ∧ LexLE [] [])) h)

private theorem k14t7_cover390 : ∀ P ∈ pathPatterns 3 4 [2], HasCheckedCertificate 14 7 ([[1], [2]] ++ P) := by
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
                exact k14t7_cover391
            · intro q
              fin_cases q
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [2] [2, 1] ∧ LexLE [2, 1] [1, 2])) h)
              · exact by
                  intro _
                  exact k14t7_cover392
        · exact by
            constructor
            · exact by
                intro _
                exact k14t7_cover393
            · intro q
              fin_cases q
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [2] [3, 1] ∧ LexLE [3, 1] [1, 3])) h)
        · exact by
            constructor
            · exact by
                intro _
                exact k14t7_cover394
            · intro q
              exact Fin.elim0 q

private theorem k14t7_cover395 : ∀ P ∈ pathPatterns 0 0 [2, 1, 1, 2], HasCheckedCertificate 14 7 ([[1], [2, 1, 1, 2]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k14t7p173, Certificates.k14t7p173_check⟩

private theorem k14t7_cover396 : ∀ P ∈ pathPatterns 1 1 [2, 1, 2], HasCheckedCertificate 14 7 ([[1], [2, 1, 2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [2, 1, 2] [] ∧ LexLE [] [])) h)

private theorem k14t7_cover397 : ∀ P ∈ pathPatterns 1 0 [2, 1, 3], HasCheckedCertificate 14 7 ([[1], [2, 1, 3]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [2, 1, 3] [] ∧ LexLE [] [])) h)

private theorem k14t7_cover398 : ∀ P ∈ pathPatterns 2 2 [2, 2], HasCheckedCertificate 14 7 ([[1], [2, 2]] ++ P) := by
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

private theorem k14t7_cover399 : ∀ P ∈ pathPatterns 1 0 [2, 2, 2], HasCheckedCertificate 14 7 ([[1], [2, 2, 2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [2, 2, 2] [] ∧ LexLE [] [])) h)

private theorem k14t7_cover400 : ∀ P ∈ pathPatterns 2 1 [2, 3], HasCheckedCertificate 14 7 ([[1], [2, 3]] ++ P) := by
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

private theorem k14t7_cover401 : ∀ P ∈ pathPatterns 2 0 [2, 4], HasCheckedCertificate 14 7 ([[1], [2, 4]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [2, 4] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k14t7_cover403 : ∀ P ∈ pathPatterns 1 0 [3], HasCheckedCertificate 14 7 ([[1], [3], [3]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [3] [] ∧ LexLE [] [])) h)

private theorem k14t7_cover402 : ∀ P ∈ pathPatterns 3 3 [3], HasCheckedCertificate 14 7 ([[1], [3]] ++ P) := by
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
                exact k14t7_cover403
            · intro q
              exact Fin.elim0 q

private theorem k14t7_cover404 : ∀ P ∈ pathPatterns 2 0 [3, 3], HasCheckedCertificate 14 7 ([[1], [3, 3]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [3, 3] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k14t7_cover405 : ∀ P ∈ pathPatterns 3 2 [4], HasCheckedCertificate 14 7 ([[1], [4]] ++ P) := by
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

private theorem k14t7_cover406 : ∀ P ∈ pathPatterns 3 1 [5], HasCheckedCertificate 14 7 ([[1], [5]] ++ P) := by
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

private theorem k14t7_cover407 : ∀ P ∈ pathPatterns 3 0 [6], HasCheckedCertificate 14 7 ([[1], [6]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [6] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k14t7_seq347 : amountSequenceForall 4 6 (fun tail =>
    (LexLE [1] ([] ++ tail) ∧ LexLE ([] ++ tail) ([] ++ tail).reverse) →
    ∀ P ∈ pathPatterns (4 - ([] ++ tail).length) (6 - ([] ++ tail).sum) ([] ++ tail),
      HasCheckedCertificate 14 7 ([[1]] ++ (([] ++ tail) :: P))) :=
by
  constructor
  · exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [1] [] ∧ LexLE [] [])) h)
  · intro q
    fin_cases q
    · exact k14t7_seq348

    · exact by
        constructor
        · exact by
            intro _
            exact k14t7_cover390
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
                          exact k14t7_cover395
                · exact by
                    constructor
                    · exact by
                        intro _
                        exact k14t7_cover396
                    · intro q
                      fin_cases q
                      · exact by
                          intro h
                          exact False.elim ((by decide : ¬ (LexLE [1] [2, 1, 2, 1] ∧ LexLE [2, 1, 2, 1] [1, 2, 1, 2])) h)
                · exact by
                    constructor
                    · exact by
                        intro _
                        exact k14t7_cover397
                    · intro q
                      exact Fin.elim0 q
          · exact by
              constructor
              · exact by
                  intro _
                  exact k14t7_cover398
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
                    constructor
                    · exact by
                        intro _
                        exact k14t7_cover399
                    · intro q
                      exact Fin.elim0 q
          · exact by
              constructor
              · exact by
                  intro _
                  exact k14t7_cover400
              · intro q
                fin_cases q
                · exact by
                    constructor
                    · exact by
                        intro h
                        exact False.elim ((by decide : ¬ (LexLE [1] [2, 3, 1] ∧ LexLE [2, 3, 1] [1, 3, 2])) h)
                    · intro q
                      exact Fin.elim0 q
          · exact by
              constructor
              · exact by
                  intro _
                  exact k14t7_cover401
              · intro q
                exact Fin.elim0 q
    · exact by
        constructor
        · exact by
            intro _
            exact k14t7_cover402
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
                    constructor
                    · exact by
                        intro h
                        exact False.elim ((by decide : ¬ (LexLE [1] [3, 1, 2] ∧ LexLE [3, 1, 2] [2, 1, 3])) h)
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
                      exact Fin.elim0 q
          · exact by
              constructor
              · exact by
                  intro _
                  exact k14t7_cover404
              · intro q
                exact Fin.elim0 q
    · exact by
        constructor
        · exact by
            intro _
            exact k14t7_cover405
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
                      exact Fin.elim0 q
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
            exact k14t7_cover406
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
            exact k14t7_cover407
        · intro q
          exact Fin.elim0 q

private theorem k14t7_cover346 : ∀ P ∈ pathPatterns 5 6 [1], HasCheckedCertificate 14 7 ([[1]] ++ P) := by
  apply pathPatterns_forall_step
  exact k14t7_seq347


private theorem k14t7_cover411 : ∀ P ∈ pathPatterns 1 3 [1, 1], HasCheckedCertificate 14 7 ([[1, 1], [1, 1]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [1, 1] [] ∧ LexLE [] [])) h)

private theorem k14t7_cover412 : ∀ P ∈ pathPatterns 0 2 [1, 1, 1], HasCheckedCertificate 14 7 ([[1, 1], [1, 1, 1]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k14t7p174, Certificates.k14t7p174_check⟩

private theorem k14t7_cover413 : ∀ P ∈ pathPatterns 0 1 [1, 1, 2], HasCheckedCertificate 14 7 ([[1, 1], [1, 1, 2]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k14t7p175, Certificates.k14t7p175_check⟩

private theorem k14t7_cover414 : ∀ P ∈ pathPatterns 0 0 [1, 1, 3], HasCheckedCertificate 14 7 ([[1, 1], [1, 1, 3]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k14t7p176, Certificates.k14t7p176_check⟩

private theorem k14t7_cover415 : ∀ P ∈ pathPatterns 1 2 [1, 2], HasCheckedCertificate 14 7 ([[1, 1], [1, 2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [1, 2] [] ∧ LexLE [] [])) h)

private theorem k14t7_cover416 : ∀ P ∈ pathPatterns 0 1 [1, 2, 1], HasCheckedCertificate 14 7 ([[1, 1], [1, 2, 1]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k14t7p177, Certificates.k14t7p177_check⟩

private theorem k14t7_cover417 : ∀ P ∈ pathPatterns 0 0 [1, 2, 2], HasCheckedCertificate 14 7 ([[1, 1], [1, 2, 2]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k14t7p178, Certificates.k14t7p178_check⟩

private theorem k14t7_cover418 : ∀ P ∈ pathPatterns 1 1 [1, 3], HasCheckedCertificate 14 7 ([[1, 1], [1, 3]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [1, 3] [] ∧ LexLE [] [])) h)

private theorem k14t7_cover419 : ∀ P ∈ pathPatterns 0 0 [1, 3, 1], HasCheckedCertificate 14 7 ([[1, 1], [1, 3, 1]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k14t7p179, Certificates.k14t7p179_check⟩

private theorem k14t7_cover420 : ∀ P ∈ pathPatterns 1 0 [1, 4], HasCheckedCertificate 14 7 ([[1, 1], [1, 4]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [1, 4] [] ∧ LexLE [] [])) h)

private theorem k14t7_cover422 : ∀ P ∈ pathPatterns 0 1 [2], HasCheckedCertificate 14 7 ([[1, 1], [2], [2]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k14t7p180, Certificates.k14t7p180_check⟩

private theorem k14t7_cover423 : ∀ P ∈ pathPatterns 0 0 [3], HasCheckedCertificate 14 7 ([[1, 1], [2], [3]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k14t7p181, Certificates.k14t7p181_check⟩

private theorem k14t7_cover421 : ∀ P ∈ pathPatterns 2 3 [2], HasCheckedCertificate 14 7 ([[1, 1], [2]] ++ P) := by
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
            exact k14t7_cover422
        · exact by
            intro _
            exact k14t7_cover423

private theorem k14t7_cover424 : ∀ P ∈ pathPatterns 0 0 [2, 1, 2], HasCheckedCertificate 14 7 ([[1, 1], [2, 1, 2]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k14t7p182, Certificates.k14t7p182_check⟩

private theorem k14t7_cover425 : ∀ P ∈ pathPatterns 1 1 [2, 2], HasCheckedCertificate 14 7 ([[1, 1], [2, 2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [2, 2] [] ∧ LexLE [] [])) h)

private theorem k14t7_cover426 : ∀ P ∈ pathPatterns 1 0 [2, 3], HasCheckedCertificate 14 7 ([[1, 1], [2, 3]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [2, 3] [] ∧ LexLE [] [])) h)

private theorem k14t7_cover427 : ∀ P ∈ pathPatterns 2 2 [3], HasCheckedCertificate 14 7 ([[1, 1], [3]] ++ P) := by
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

private theorem k14t7_cover428 : ∀ P ∈ pathPatterns 2 1 [4], HasCheckedCertificate 14 7 ([[1, 1], [4]] ++ P) := by
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

private theorem k14t7_cover429 : ∀ P ∈ pathPatterns 2 0 [5], HasCheckedCertificate 14 7 ([[1, 1], [5]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [5] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k14t7_seq410 : amountSequenceForall 3 5 (fun tail =>
    (LexLE [1, 1] ([] ++ tail) ∧ LexLE ([] ++ tail) ([] ++ tail).reverse) →
    ∀ P ∈ pathPatterns (3 - ([] ++ tail).length) (5 - ([] ++ tail).sum) ([] ++ tail),
      HasCheckedCertificate 14 7 ([[1, 1]] ++ (([] ++ tail) :: P))) :=
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
                  exact k14t7_cover411
              · intro q
                fin_cases q
                · exact by
                    intro _
                    exact k14t7_cover412
                · exact by
                    intro _
                    exact k14t7_cover413
                · exact by
                    intro _
                    exact k14t7_cover414
          · exact by
              constructor
              · exact by
                  intro _
                  exact k14t7_cover415
              · intro q
                fin_cases q
                · exact by
                    intro _
                    exact k14t7_cover416
                · exact by
                    intro _
                    exact k14t7_cover417
          · exact by
              constructor
              · exact by
                  intro _
                  exact k14t7_cover418
              · intro q
                fin_cases q
                · exact by
                    intro _
                    exact k14t7_cover419
          · exact by
              constructor
              · exact by
                  intro _
                  exact k14t7_cover420
              · intro q
                exact Fin.elim0 q
    · exact by
        constructor
        · exact by
            intro _
            exact k14t7_cover421
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
                    exact k14t7_cover424
          · exact by
              constructor
              · exact by
                  intro _
                  exact k14t7_cover425
              · intro q
                fin_cases q
                · exact by
                    intro h
                    exact False.elim ((by decide : ¬ (LexLE [1, 1] [2, 2, 1] ∧ LexLE [2, 2, 1] [1, 2, 2])) h)
          · exact by
              constructor
              · exact by
                  intro _
                  exact k14t7_cover426
              · intro q
                exact Fin.elim0 q
    · exact by
        constructor
        · exact by
            intro _
            exact k14t7_cover427
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
              constructor
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [1, 1] [3, 2] ∧ LexLE [3, 2] [2, 3])) h)
              · intro q
                exact Fin.elim0 q
    · exact by
        constructor
        · exact by
            intro _
            exact k14t7_cover428
        · intro q
          fin_cases q
          · exact by
              constructor
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [1, 1] [4, 1] ∧ LexLE [4, 1] [1, 4])) h)
              · intro q
                exact Fin.elim0 q
    · exact by
        constructor
        · exact by
            intro _
            exact k14t7_cover429
        · intro q
          exact Fin.elim0 q

private theorem k14t7_cover409 : ∀ P ∈ pathPatterns 4 5 [1, 1], HasCheckedCertificate 14 7 ([[1, 1]] ++ P) := by
  apply pathPatterns_forall_step
  exact k14t7_seq410


private theorem k14t7_cover431 : ∀ P ∈ pathPatterns 0 1 [1, 2], HasCheckedCertificate 14 7 ([[1, 1, 1], [1, 2]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k14t7p183, Certificates.k14t7p183_check⟩

private theorem k14t7_cover432 : ∀ P ∈ pathPatterns 0 0 [1, 3], HasCheckedCertificate 14 7 ([[1, 1, 1], [1, 3]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k14t7p184, Certificates.k14t7p184_check⟩

private theorem k14t7_cover433 : ∀ P ∈ pathPatterns 1 2 [2], HasCheckedCertificate 14 7 ([[1, 1, 1], [2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [2] [] ∧ LexLE [] [])) h)

private theorem k14t7_cover434 : ∀ P ∈ pathPatterns 0 0 [2, 2], HasCheckedCertificate 14 7 ([[1, 1, 1], [2, 2]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k14t7p185, Certificates.k14t7p185_check⟩

private theorem k14t7_cover435 : ∀ P ∈ pathPatterns 1 1 [3], HasCheckedCertificate 14 7 ([[1, 1, 1], [3]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [3] [] ∧ LexLE [] [])) h)

private theorem k14t7_cover436 : ∀ P ∈ pathPatterns 1 0 [4], HasCheckedCertificate 14 7 ([[1, 1, 1], [4]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [4] [] ∧ LexLE [] [])) h)

private theorem k14t7_cover430 : ∀ P ∈ pathPatterns 3 4 [1, 1, 1], HasCheckedCertificate 14 7 ([[1, 1, 1]] ++ P) := by
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
                  exact k14t7_cover431
              · exact by
                  intro _
                  exact k14t7_cover432
        · exact by
            constructor
            · exact by
                intro _
                exact k14t7_cover433
            · intro q
              fin_cases q
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [1, 1, 1] [2, 1] ∧ LexLE [2, 1] [1, 2])) h)
              · exact by
                  intro _
                  exact k14t7_cover434
        · exact by
            constructor
            · exact by
                intro _
                exact k14t7_cover435
            · intro q
              fin_cases q
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [1, 1, 1] [3, 1] ∧ LexLE [3, 1] [1, 3])) h)
        · exact by
            constructor
            · exact by
                intro _
                exact k14t7_cover436
            · intro q
              exact Fin.elim0 q

private theorem k14t7_cover438 : ∀ P ∈ pathPatterns 0 1 [2], HasCheckedCertificate 14 7 ([[1, 1, 1, 1], [2]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k14t7p186, Certificates.k14t7p186_check⟩

private theorem k14t7_cover439 : ∀ P ∈ pathPatterns 0 0 [3], HasCheckedCertificate 14 7 ([[1, 1, 1, 1], [3]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k14t7p187, Certificates.k14t7p187_check⟩

private theorem k14t7_cover437 : ∀ P ∈ pathPatterns 2 3 [1, 1, 1, 1], HasCheckedCertificate 14 7 ([[1, 1, 1, 1]] ++ P) := by
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
            exact k14t7_cover438
        · exact by
            intro _
            exact k14t7_cover439

private theorem k14t7_cover440 : ∀ P ∈ pathPatterns 1 2 [1, 1, 1, 1, 1], HasCheckedCertificate 14 7 ([[1, 1, 1, 1, 1]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [1, 1, 1, 1, 1] [] ∧ LexLE [] [])) h)

private theorem k14t7_cover441 : ∀ P ∈ pathPatterns 0 1 [1, 1, 1, 1, 1, 1], HasCheckedCertificate 14 7 ([[1, 1, 1, 1, 1, 1]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k14t7p188, Certificates.k14t7p188_check⟩

private theorem k14t7_cover442 : ∀ P ∈ pathPatterns 0 0 [1, 1, 1, 1, 1, 2], HasCheckedCertificate 14 7 ([[1, 1, 1, 1, 1, 2]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k14t7p189, Certificates.k14t7p189_check⟩

private theorem k14t7_cover443 : ∀ P ∈ pathPatterns 1 1 [1, 1, 1, 1, 2], HasCheckedCertificate 14 7 ([[1, 1, 1, 1, 2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [1, 1, 1, 1, 2] [] ∧ LexLE [] [])) h)

private theorem k14t7_cover444 : ∀ P ∈ pathPatterns 0 0 [1, 1, 1, 1, 2, 1], HasCheckedCertificate 14 7 ([[1, 1, 1, 1, 2, 1]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k14t7p190, Certificates.k14t7p190_check⟩

private theorem k14t7_cover445 : ∀ P ∈ pathPatterns 1 0 [1, 1, 1, 1, 3], HasCheckedCertificate 14 7 ([[1, 1, 1, 1, 3]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [1, 1, 1, 1, 3] [] ∧ LexLE [] [])) h)

private theorem k14t7_cover447 : ∀ P ∈ pathPatterns 0 0 [2], HasCheckedCertificate 14 7 ([[1, 1, 1, 2], [2]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k14t7p191, Certificates.k14t7p191_check⟩

private theorem k14t7_cover446 : ∀ P ∈ pathPatterns 2 2 [1, 1, 1, 2], HasCheckedCertificate 14 7 ([[1, 1, 1, 2]] ++ P) := by
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
            exact k14t7_cover447

private theorem k14t7_cover448 : ∀ P ∈ pathPatterns 1 1 [1, 1, 1, 2, 1], HasCheckedCertificate 14 7 ([[1, 1, 1, 2, 1]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [1, 1, 1, 2, 1] [] ∧ LexLE [] [])) h)

private theorem k14t7_cover449 : ∀ P ∈ pathPatterns 0 0 [1, 1, 1, 2, 1, 1], HasCheckedCertificate 14 7 ([[1, 1, 1, 2, 1, 1]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k14t7p192, Certificates.k14t7p192_check⟩

private theorem k14t7_cover450 : ∀ P ∈ pathPatterns 1 0 [1, 1, 1, 2, 2], HasCheckedCertificate 14 7 ([[1, 1, 1, 2, 2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [1, 1, 1, 2, 2] [] ∧ LexLE [] [])) h)

private theorem k14t7_cover451 : ∀ P ∈ pathPatterns 2 1 [1, 1, 1, 3], HasCheckedCertificate 14 7 ([[1, 1, 1, 3]] ++ P) := by
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

private theorem k14t7_cover452 : ∀ P ∈ pathPatterns 1 0 [1, 1, 1, 3, 1], HasCheckedCertificate 14 7 ([[1, 1, 1, 3, 1]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [1, 1, 1, 3, 1] [] ∧ LexLE [] [])) h)

private theorem k14t7_cover453 : ∀ P ∈ pathPatterns 2 0 [1, 1, 1, 4], HasCheckedCertificate 14 7 ([[1, 1, 1, 4]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [1, 1, 1, 4] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k14t7_cover455 : ∀ P ∈ pathPatterns 0 0 [1, 2], HasCheckedCertificate 14 7 ([[1, 1, 2], [1, 2]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k14t7p193, Certificates.k14t7p193_check⟩

private theorem k14t7_cover456 : ∀ P ∈ pathPatterns 1 1 [2], HasCheckedCertificate 14 7 ([[1, 1, 2], [2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [2] [] ∧ LexLE [] [])) h)

private theorem k14t7_cover457 : ∀ P ∈ pathPatterns 1 0 [3], HasCheckedCertificate 14 7 ([[1, 1, 2], [3]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [3] [] ∧ LexLE [] [])) h)

private theorem k14t7_cover454 : ∀ P ∈ pathPatterns 3 3 [1, 1, 2], HasCheckedCertificate 14 7 ([[1, 1, 2]] ++ P) := by
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
                  exact k14t7_cover455
        · exact by
            constructor
            · exact by
                intro _
                exact k14t7_cover456
            · intro q
              fin_cases q
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [1, 1, 2] [2, 1] ∧ LexLE [2, 1] [1, 2])) h)
        · exact by
            constructor
            · exact by
                intro _
                exact k14t7_cover457
            · intro q
              exact Fin.elim0 q

private theorem k14t7_cover459 : ∀ P ∈ pathPatterns 0 0 [2], HasCheckedCertificate 14 7 ([[1, 1, 2, 1], [2]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k14t7p194, Certificates.k14t7p194_check⟩

private theorem k14t7_cover458 : ∀ P ∈ pathPatterns 2 2 [1, 1, 2, 1], HasCheckedCertificate 14 7 ([[1, 1, 2, 1]] ++ P) := by
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
            exact k14t7_cover459

private theorem k14t7_cover460 : ∀ P ∈ pathPatterns 1 1 [1, 1, 2, 1, 1], HasCheckedCertificate 14 7 ([[1, 1, 2, 1, 1]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [1, 1, 2, 1, 1] [] ∧ LexLE [] [])) h)

private theorem k14t7_cover461 : ∀ P ∈ pathPatterns 1 0 [1, 1, 2, 1, 2], HasCheckedCertificate 14 7 ([[1, 1, 2, 1, 2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [1, 1, 2, 1, 2] [] ∧ LexLE [] [])) h)

private theorem k14t7_cover462 : ∀ P ∈ pathPatterns 2 1 [1, 1, 2, 2], HasCheckedCertificate 14 7 ([[1, 1, 2, 2]] ++ P) := by
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

private theorem k14t7_cover463 : ∀ P ∈ pathPatterns 1 0 [1, 1, 2, 2, 1], HasCheckedCertificate 14 7 ([[1, 1, 2, 2, 1]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [1, 1, 2, 2, 1] [] ∧ LexLE [] [])) h)

private theorem k14t7_cover464 : ∀ P ∈ pathPatterns 2 0 [1, 1, 2, 3], HasCheckedCertificate 14 7 ([[1, 1, 2, 3]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [1, 1, 2, 3] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k14t7_cover466 : ∀ P ∈ pathPatterns 1 0 [2], HasCheckedCertificate 14 7 ([[1, 1, 3], [2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [2] [] ∧ LexLE [] [])) h)

private theorem k14t7_cover465 : ∀ P ∈ pathPatterns 3 2 [1, 1, 3], HasCheckedCertificate 14 7 ([[1, 1, 3]] ++ P) := by
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
            constructor
            · exact by
                intro _
                exact k14t7_cover466
            · intro q
              exact Fin.elim0 q

private theorem k14t7_cover467 : ∀ P ∈ pathPatterns 2 1 [1, 1, 3, 1], HasCheckedCertificate 14 7 ([[1, 1, 3, 1]] ++ P) := by
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

private theorem k14t7_cover468 : ∀ P ∈ pathPatterns 1 0 [1, 1, 3, 1, 1], HasCheckedCertificate 14 7 ([[1, 1, 3, 1, 1]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [1, 1, 3, 1, 1] [] ∧ LexLE [] [])) h)

private theorem k14t7_cover469 : ∀ P ∈ pathPatterns 2 0 [1, 1, 3, 2], HasCheckedCertificate 14 7 ([[1, 1, 3, 2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [1, 1, 3, 2] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k14t7_cover470 : ∀ P ∈ pathPatterns 3 1 [1, 1, 4], HasCheckedCertificate 14 7 ([[1, 1, 4]] ++ P) := by
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
              exact Fin.elim0 q

private theorem k14t7_cover471 : ∀ P ∈ pathPatterns 2 0 [1, 1, 4, 1], HasCheckedCertificate 14 7 ([[1, 1, 4, 1]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [1, 1, 4, 1] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k14t7_cover472 : ∀ P ∈ pathPatterns 3 0 [1, 1, 5], HasCheckedCertificate 14 7 ([[1, 1, 5]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [1, 1, 5] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k14t7_seq408 : amountSequenceForall 4 5 (fun tail =>
    (LexLE [] ([1, 1] ++ tail) ∧ LexLE ([1, 1] ++ tail) ([1, 1] ++ tail).reverse) →
    ∀ P ∈ pathPatterns (6 - ([1, 1] ++ tail).length) (7 - ([1, 1] ++ tail).sum) ([1, 1] ++ tail),
      HasCheckedCertificate 14 7 ([] ++ (([1, 1] ++ tail) :: P))) :=
by
  constructor
  · exact by
      intro _
      exact k14t7_cover409
  · intro q
    fin_cases q
    · exact by
        constructor
        · exact by
            intro _
            exact k14t7_cover430
        · intro q
          fin_cases q
          · exact by
              constructor
              · exact by
                  intro _
                  exact k14t7_cover437
              · intro q
                fin_cases q
                · exact by
                    constructor
                    · exact by
                        intro _
                        exact k14t7_cover440
                    · intro q
                      fin_cases q
                      · exact by
                          intro _
                          exact k14t7_cover441
                      · exact by
                          intro _
                          exact k14t7_cover442
                · exact by
                    constructor
                    · exact by
                        intro _
                        exact k14t7_cover443
                    · intro q
                      fin_cases q
                      · exact by
                          intro _
                          exact k14t7_cover444
                · exact by
                    constructor
                    · exact by
                        intro _
                        exact k14t7_cover445
                    · intro q
                      exact Fin.elim0 q
          · exact by
              constructor
              · exact by
                  intro _
                  exact k14t7_cover446
              · intro q
                fin_cases q
                · exact by
                    constructor
                    · exact by
                        intro _
                        exact k14t7_cover448
                    · intro q
                      fin_cases q
                      · exact by
                          intro _
                          exact k14t7_cover449
                · exact by
                    constructor
                    · exact by
                        intro _
                        exact k14t7_cover450
                    · intro q
                      exact Fin.elim0 q
          · exact by
              constructor
              · exact by
                  intro _
                  exact k14t7_cover451
              · intro q
                fin_cases q
                · exact by
                    constructor
                    · exact by
                        intro _
                        exact k14t7_cover452
                    · intro q
                      exact Fin.elim0 q
          · exact by
              constructor
              · exact by
                  intro _
                  exact k14t7_cover453
              · intro q
                exact Fin.elim0 q
    · exact by
        constructor
        · exact by
            intro _
            exact k14t7_cover454
        · intro q
          fin_cases q
          · exact by
              constructor
              · exact by
                  intro _
                  exact k14t7_cover458
              · intro q
                fin_cases q
                · exact by
                    constructor
                    · exact by
                        intro _
                        exact k14t7_cover460
                    · intro q
                      fin_cases q
                      · exact by
                          intro h
                          exact False.elim ((by decide : ¬ (LexLE [] [1, 1, 2, 1, 1, 1] ∧ LexLE [1, 1, 2, 1, 1, 1] [1, 1, 1, 2, 1, 1])) h)
                · exact by
                    constructor
                    · exact by
                        intro _
                        exact k14t7_cover461
                    · intro q
                      exact Fin.elim0 q
          · exact by
              constructor
              · exact by
                  intro _
                  exact k14t7_cover462
              · intro q
                fin_cases q
                · exact by
                    constructor
                    · exact by
                        intro _
                        exact k14t7_cover463
                    · intro q
                      exact Fin.elim0 q
          · exact by
              constructor
              · exact by
                  intro _
                  exact k14t7_cover464
              · intro q
                exact Fin.elim0 q
    · exact by
        constructor
        · exact by
            intro _
            exact k14t7_cover465
        · intro q
          fin_cases q
          · exact by
              constructor
              · exact by
                  intro _
                  exact k14t7_cover467
              · intro q
                fin_cases q
                · exact by
                    constructor
                    · exact by
                        intro _
                        exact k14t7_cover468
                    · intro q
                      exact Fin.elim0 q
          · exact by
              constructor
              · exact by
                  intro _
                  exact k14t7_cover469
              · intro q
                exact Fin.elim0 q
    · exact by
        constructor
        · exact by
            intro _
            exact k14t7_cover470
        · intro q
          fin_cases q
          · exact by
              constructor
              · exact by
                  intro _
                  exact k14t7_cover471
              · intro q
                exact Fin.elim0 q
    · exact by
        constructor
        · exact by
            intro _
            exact k14t7_cover472
        · intro q
          exact Fin.elim0 q

private theorem k14t7_cover474 : ∀ P ∈ pathPatterns 1 1 [1, 2], HasCheckedCertificate 14 7 ([[1, 2], [1, 2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [1, 2] [] ∧ LexLE [] [])) h)

private theorem k14t7_cover475 : ∀ P ∈ pathPatterns 0 0 [1, 2, 1], HasCheckedCertificate 14 7 ([[1, 2], [1, 2, 1]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k14t7p195, Certificates.k14t7p195_check⟩

private theorem k14t7_cover476 : ∀ P ∈ pathPatterns 1 0 [1, 3], HasCheckedCertificate 14 7 ([[1, 2], [1, 3]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [1, 3] [] ∧ LexLE [] [])) h)

private theorem k14t7_cover478 : ∀ P ∈ pathPatterns 0 0 [2], HasCheckedCertificate 14 7 ([[1, 2], [2], [2]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k14t7p196, Certificates.k14t7p196_check⟩

private theorem k14t7_cover477 : ∀ P ∈ pathPatterns 2 2 [2], HasCheckedCertificate 14 7 ([[1, 2], [2]] ++ P) := by
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
            exact k14t7_cover478

private theorem k14t7_cover479 : ∀ P ∈ pathPatterns 1 0 [2, 2], HasCheckedCertificate 14 7 ([[1, 2], [2, 2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [2, 2] [] ∧ LexLE [] [])) h)

private theorem k14t7_cover480 : ∀ P ∈ pathPatterns 2 1 [3], HasCheckedCertificate 14 7 ([[1, 2], [3]] ++ P) := by
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

private theorem k14t7_cover481 : ∀ P ∈ pathPatterns 2 0 [4], HasCheckedCertificate 14 7 ([[1, 2], [4]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [4] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k14t7_cover473 : ∀ P ∈ pathPatterns 4 4 [1, 2], HasCheckedCertificate 14 7 ([[1, 2]] ++ P) := by
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
                  constructor
                  · exact by
                      intro _
                      exact k14t7_cover474
                  · intro q
                    fin_cases q
                    · exact by
                        intro _
                        exact k14t7_cover475
              · exact by
                  constructor
                  · exact by
                      intro _
                      exact k14t7_cover476
                  · intro q
                    exact Fin.elim0 q
        · exact by
            constructor
            · exact by
                intro _
                exact k14t7_cover477
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
                  constructor
                  · exact by
                      intro _
                      exact k14t7_cover479
                  · intro q
                    exact Fin.elim0 q
        · exact by
            constructor
            · exact by
                intro _
                exact k14t7_cover480
            · intro q
              fin_cases q
              · exact by
                  constructor
                  · exact by
                      intro h
                      exact False.elim ((by decide : ¬ (LexLE [1, 2] [3, 1] ∧ LexLE [3, 1] [1, 3])) h)
                  · intro q
                    exact Fin.elim0 q
        · exact by
            constructor
            · exact by
                intro _
                exact k14t7_cover481
            · intro q
              exact Fin.elim0 q

private theorem k14t7_cover483 : ∀ P ∈ pathPatterns 1 1 [2], HasCheckedCertificate 14 7 ([[1, 2, 1], [2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [2] [] ∧ LexLE [] [])) h)

private theorem k14t7_cover484 : ∀ P ∈ pathPatterns 1 0 [3], HasCheckedCertificate 14 7 ([[1, 2, 1], [3]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [3] [] ∧ LexLE [] [])) h)

private theorem k14t7_cover482 : ∀ P ∈ pathPatterns 3 3 [1, 2, 1], HasCheckedCertificate 14 7 ([[1, 2, 1]] ++ P) := by
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
            constructor
            · exact by
                intro _
                exact k14t7_cover483
            · intro q
              fin_cases q
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [1, 2, 1] [2, 1] ∧ LexLE [2, 1] [1, 2])) h)
        · exact by
            constructor
            · exact by
                intro _
                exact k14t7_cover484
            · intro q
              exact Fin.elim0 q

private theorem k14t7_cover485 : ∀ P ∈ pathPatterns 1 0 [1, 2, 1, 1, 2], HasCheckedCertificate 14 7 ([[1, 2, 1, 1, 2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [1, 2, 1, 1, 2] [] ∧ LexLE [] [])) h)

private theorem k14t7_cover486 : ∀ P ∈ pathPatterns 2 1 [1, 2, 1, 2], HasCheckedCertificate 14 7 ([[1, 2, 1, 2]] ++ P) := by
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

private theorem k14t7_cover487 : ∀ P ∈ pathPatterns 1 0 [1, 2, 1, 2, 1], HasCheckedCertificate 14 7 ([[1, 2, 1, 2, 1]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [1, 2, 1, 2, 1] [] ∧ LexLE [] [])) h)

private theorem k14t7_cover488 : ∀ P ∈ pathPatterns 2 0 [1, 2, 1, 3], HasCheckedCertificate 14 7 ([[1, 2, 1, 3]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [1, 2, 1, 3] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k14t7_cover490 : ∀ P ∈ pathPatterns 1 0 [2], HasCheckedCertificate 14 7 ([[1, 2, 2], [2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [2] [] ∧ LexLE [] [])) h)

private theorem k14t7_cover489 : ∀ P ∈ pathPatterns 3 2 [1, 2, 2], HasCheckedCertificate 14 7 ([[1, 2, 2]] ++ P) := by
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
            constructor
            · exact by
                intro _
                exact k14t7_cover490
            · intro q
              exact Fin.elim0 q

private theorem k14t7_cover491 : ∀ P ∈ pathPatterns 2 1 [1, 2, 2, 1], HasCheckedCertificate 14 7 ([[1, 2, 2, 1]] ++ P) := by
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

private theorem k14t7_cover492 : ∀ P ∈ pathPatterns 2 0 [1, 2, 2, 2], HasCheckedCertificate 14 7 ([[1, 2, 2, 2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [1, 2, 2, 2] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k14t7_cover493 : ∀ P ∈ pathPatterns 3 1 [1, 2, 3], HasCheckedCertificate 14 7 ([[1, 2, 3]] ++ P) := by
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
              exact Fin.elim0 q

private theorem k14t7_cover494 : ∀ P ∈ pathPatterns 2 0 [1, 2, 3, 1], HasCheckedCertificate 14 7 ([[1, 2, 3, 1]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [1, 2, 3, 1] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k14t7_cover495 : ∀ P ∈ pathPatterns 3 0 [1, 2, 4], HasCheckedCertificate 14 7 ([[1, 2, 4]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [1, 2, 4] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k14t7_cover497 : ∀ P ∈ pathPatterns 2 1 [2], HasCheckedCertificate 14 7 ([[1, 3], [2]] ++ P) := by
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

private theorem k14t7_cover498 : ∀ P ∈ pathPatterns 2 0 [3], HasCheckedCertificate 14 7 ([[1, 3], [3]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [3] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k14t7_cover496 : ∀ P ∈ pathPatterns 4 3 [1, 3], HasCheckedCertificate 14 7 ([[1, 3]] ++ P) := by
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
                  constructor
                  · exact by
                      intro h
                      exact False.elim ((by decide : ¬ (LexLE [1, 3] [1, 2] ∧ LexLE [1, 2] [2, 1])) h)
                  · intro q
                    exact Fin.elim0 q
        · exact by
            constructor
            · exact by
                intro _
                exact k14t7_cover497
            · intro q
              fin_cases q
              · exact by
                  constructor
                  · exact by
                      intro h
                      exact False.elim ((by decide : ¬ (LexLE [1, 3] [2, 1] ∧ LexLE [2, 1] [1, 2])) h)
                  · intro q
                    exact Fin.elim0 q
        · exact by
            constructor
            · exact by
                intro _
                exact k14t7_cover498
            · intro q
              exact Fin.elim0 q

private theorem k14t7_cover500 : ∀ P ∈ pathPatterns 1 0 [2], HasCheckedCertificate 14 7 ([[1, 3, 1], [2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [2] [] ∧ LexLE [] [])) h)

private theorem k14t7_cover499 : ∀ P ∈ pathPatterns 3 2 [1, 3, 1], HasCheckedCertificate 14 7 ([[1, 3, 1]] ++ P) := by
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
            constructor
            · exact by
                intro _
                exact k14t7_cover500
            · intro q
              exact Fin.elim0 q

private theorem k14t7_cover501 : ∀ P ∈ pathPatterns 2 0 [1, 3, 1, 2], HasCheckedCertificate 14 7 ([[1, 3, 1, 2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [1, 3, 1, 2] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k14t7_cover502 : ∀ P ∈ pathPatterns 3 1 [1, 3, 2], HasCheckedCertificate 14 7 ([[1, 3, 2]] ++ P) := by
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
              exact Fin.elim0 q

private theorem k14t7_cover503 : ∀ P ∈ pathPatterns 3 0 [1, 3, 3], HasCheckedCertificate 14 7 ([[1, 3, 3]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [1, 3, 3] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k14t7_cover505 : ∀ P ∈ pathPatterns 2 0 [2], HasCheckedCertificate 14 7 ([[1, 4], [2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [2] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k14t7_cover504 : ∀ P ∈ pathPatterns 4 2 [1, 4], HasCheckedCertificate 14 7 ([[1, 4]] ++ P) := by
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
                    exact Fin.elim0 q
        · exact by
            constructor
            · exact by
                intro _
                exact k14t7_cover505
            · intro q
              exact Fin.elim0 q

private theorem k14t7_cover506 : ∀ P ∈ pathPatterns 3 1 [1, 4, 1], HasCheckedCertificate 14 7 ([[1, 4, 1]] ++ P) := by
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
              exact Fin.elim0 q

private theorem k14t7_cover507 : ∀ P ∈ pathPatterns 3 0 [1, 4, 2], HasCheckedCertificate 14 7 ([[1, 4, 2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [1, 4, 2] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k14t7_cover508 : ∀ P ∈ pathPatterns 4 1 [1, 5], HasCheckedCertificate 14 7 ([[1, 5]] ++ P) := by
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

private theorem k14t7_cover509 : ∀ P ∈ pathPatterns 3 0 [1, 5, 1], HasCheckedCertificate 14 7 ([[1, 5, 1]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [1, 5, 1] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k14t7_cover510 : ∀ P ∈ pathPatterns 4 0 [1, 6], HasCheckedCertificate 14 7 ([[1, 6]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [1, 6] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k14t7_seq345 : amountSequenceForall 5 6 (fun tail =>
    (LexLE [] ([1] ++ tail) ∧ LexLE ([1] ++ tail) ([1] ++ tail).reverse) →
    ∀ P ∈ pathPatterns (6 - ([1] ++ tail).length) (7 - ([1] ++ tail).sum) ([1] ++ tail),
      HasCheckedCertificate 14 7 ([] ++ (([1] ++ tail) :: P))) :=
by
  constructor
  · exact by
      intro _
      exact k14t7_cover346
  · intro q
    fin_cases q
    · exact k14t7_seq408

    · exact by
        constructor
        · exact by
            intro _
            exact k14t7_cover473
        · intro q
          fin_cases q
          · exact by
              constructor
              · exact by
                  intro _
                  exact k14t7_cover482
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
                          constructor
                          · exact by
                              intro _
                              exact k14t7_cover485
                          · intro q
                            exact Fin.elim0 q
                · exact by
                    constructor
                    · exact by
                        intro _
                        exact k14t7_cover486
                    · intro q
                      fin_cases q
                      · exact by
                          constructor
                          · exact by
                              intro _
                              exact k14t7_cover487
                          · intro q
                            exact Fin.elim0 q
                · exact by
                    constructor
                    · exact by
                        intro _
                        exact k14t7_cover488
                    · intro q
                      exact Fin.elim0 q
          · exact by
              constructor
              · exact by
                  intro _
                  exact k14t7_cover489
              · intro q
                fin_cases q
                · exact by
                    constructor
                    · exact by
                        intro _
                        exact k14t7_cover491
                    · intro q
                      fin_cases q
                      · exact by
                          constructor
                          · exact by
                              intro h
                              exact False.elim ((by decide : ¬ (LexLE [] [1, 2, 2, 1, 1] ∧ LexLE [1, 2, 2, 1, 1] [1, 1, 2, 2, 1])) h)
                          · intro q
                            exact Fin.elim0 q
                · exact by
                    constructor
                    · exact by
                        intro _
                        exact k14t7_cover492
                    · intro q
                      exact Fin.elim0 q
          · exact by
              constructor
              · exact by
                  intro _
                  exact k14t7_cover493
              · intro q
                fin_cases q
                · exact by
                    constructor
                    · exact by
                        intro _
                        exact k14t7_cover494
                    · intro q
                      exact Fin.elim0 q
          · exact by
              constructor
              · exact by
                  intro _
                  exact k14t7_cover495
              · intro q
                exact Fin.elim0 q
    · exact by
        constructor
        · exact by
            intro _
            exact k14t7_cover496
        · intro q
          fin_cases q
          · exact by
              constructor
              · exact by
                  intro _
                  exact k14t7_cover499
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
                            exact Fin.elim0 q
                · exact by
                    constructor
                    · exact by
                        intro _
                        exact k14t7_cover501
                    · intro q
                      exact Fin.elim0 q
          · exact by
              constructor
              · exact by
                  intro _
                  exact k14t7_cover502
              · intro q
                fin_cases q
                · exact by
                    constructor
                    · exact by
                        intro h
                        exact False.elim ((by decide : ¬ (LexLE [] [1, 3, 2, 1] ∧ LexLE [1, 3, 2, 1] [1, 2, 3, 1])) h)
                    · intro q
                      exact Fin.elim0 q
          · exact by
              constructor
              · exact by
                  intro _
                  exact k14t7_cover503
              · intro q
                exact Fin.elim0 q
    · exact by
        constructor
        · exact by
            intro _
            exact k14t7_cover504
        · intro q
          fin_cases q
          · exact by
              constructor
              · exact by
                  intro _
                  exact k14t7_cover506
              · intro q
                fin_cases q
                · exact by
                    constructor
                    · exact by
                        intro h
                        exact False.elim ((by decide : ¬ (LexLE [] [1, 4, 1, 1] ∧ LexLE [1, 4, 1, 1] [1, 1, 4, 1])) h)
                    · intro q
                      exact Fin.elim0 q
          · exact by
              constructor
              · exact by
                  intro _
                  exact k14t7_cover507
              · intro q
                exact Fin.elim0 q
    · exact by
        constructor
        · exact by
            intro _
            exact k14t7_cover508
        · intro q
          fin_cases q
          · exact by
              constructor
              · exact by
                  intro _
                  exact k14t7_cover509
              · intro q
                exact Fin.elim0 q
    · exact by
        constructor
        · exact by
            intro _
            exact k14t7_cover510
        · intro q
          exact Fin.elim0 q

private theorem k14t7_cover515 : ∀ P ∈ pathPatterns 1 1 [2], HasCheckedCertificate 14 7 ([[2], [2], [2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [2] [] ∧ LexLE [] [])) h)

private theorem k14t7_cover516 : ∀ P ∈ pathPatterns 1 0 [3], HasCheckedCertificate 14 7 ([[2], [2], [3]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [3] [] ∧ LexLE [] [])) h)

private theorem k14t7_cover514 : ∀ P ∈ pathPatterns 3 3 [2], HasCheckedCertificate 14 7 ([[2], [2]] ++ P) := by
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
                exact k14t7_cover515
            · intro q
              fin_cases q
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [2] [2, 1] ∧ LexLE [2, 1] [1, 2])) h)
        · exact by
            constructor
            · exact by
                intro _
                exact k14t7_cover516
            · intro q
              exact Fin.elim0 q

private theorem k14t7_cover517 : ∀ P ∈ pathPatterns 1 0 [2, 1, 2], HasCheckedCertificate 14 7 ([[2], [2, 1, 2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [2, 1, 2] [] ∧ LexLE [] [])) h)

private theorem k14t7_cover518 : ∀ P ∈ pathPatterns 2 1 [2, 2], HasCheckedCertificate 14 7 ([[2], [2, 2]] ++ P) := by
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

private theorem k14t7_cover519 : ∀ P ∈ pathPatterns 2 0 [2, 3], HasCheckedCertificate 14 7 ([[2], [2, 3]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [2, 3] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k14t7_cover520 : ∀ P ∈ pathPatterns 3 2 [3], HasCheckedCertificate 14 7 ([[2], [3]] ++ P) := by
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

private theorem k14t7_cover521 : ∀ P ∈ pathPatterns 3 1 [4], HasCheckedCertificate 14 7 ([[2], [4]] ++ P) := by
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

private theorem k14t7_cover522 : ∀ P ∈ pathPatterns 3 0 [5], HasCheckedCertificate 14 7 ([[2], [5]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [5] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k14t7_seq513 : amountSequenceForall 4 5 (fun tail =>
    (LexLE [2] ([] ++ tail) ∧ LexLE ([] ++ tail) ([] ++ tail).reverse) →
    ∀ P ∈ pathPatterns (4 - ([] ++ tail).length) (5 - ([] ++ tail).sum) ([] ++ tail),
      HasCheckedCertificate 14 7 ([[2]] ++ (([] ++ tail) :: P))) :=
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
                    constructor
                    · exact by
                        intro h
                        exact False.elim ((by decide : ¬ (LexLE [2] [1, 1, 3] ∧ LexLE [1, 1, 3] [3, 1, 1])) h)
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
                    constructor
                    · exact by
                        intro h
                        exact False.elim ((by decide : ¬ (LexLE [2] [1, 2, 2] ∧ LexLE [1, 2, 2] [2, 2, 1])) h)
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
                      exact Fin.elim0 q
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
            exact k14t7_cover514
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
                    constructor
                    · exact by
                        intro _
                        exact k14t7_cover517
                    · intro q
                      exact Fin.elim0 q
          · exact by
              constructor
              · exact by
                  intro _
                  exact k14t7_cover518
              · intro q
                fin_cases q
                · exact by
                    constructor
                    · exact by
                        intro h
                        exact False.elim ((by decide : ¬ (LexLE [2] [2, 2, 1] ∧ LexLE [2, 2, 1] [1, 2, 2])) h)
                    · intro q
                      exact Fin.elim0 q
          · exact by
              constructor
              · exact by
                  intro _
                  exact k14t7_cover519
              · intro q
                exact Fin.elim0 q
    · exact by
        constructor
        · exact by
            intro _
            exact k14t7_cover520
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
                      exact Fin.elim0 q
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
            exact k14t7_cover521
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
            exact k14t7_cover522
        · intro q
          exact Fin.elim0 q

private theorem k14t7_cover512 : ∀ P ∈ pathPatterns 5 5 [2], HasCheckedCertificate 14 7 ([[2]] ++ P) := by
  apply pathPatterns_forall_step
  exact k14t7_seq513


private theorem k14t7_cover523 : ∀ P ∈ pathPatterns 1 0 [2, 1, 1, 1, 2], HasCheckedCertificate 14 7 ([[2, 1, 1, 1, 2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [2, 1, 1, 1, 2] [] ∧ LexLE [] [])) h)

private theorem k14t7_cover524 : ∀ P ∈ pathPatterns 2 1 [2, 1, 1, 2], HasCheckedCertificate 14 7 ([[2, 1, 1, 2]] ++ P) := by
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

private theorem k14t7_cover525 : ∀ P ∈ pathPatterns 2 0 [2, 1, 1, 3], HasCheckedCertificate 14 7 ([[2, 1, 1, 3]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [2, 1, 1, 3] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k14t7_cover526 : ∀ P ∈ pathPatterns 3 2 [2, 1, 2], HasCheckedCertificate 14 7 ([[2, 1, 2]] ++ P) := by
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
            constructor
            · exact by
                intro h
                exact False.elim ((by decide : ¬ (LexLE [2, 1, 2] [2] ∧ LexLE [2] [2])) h)
            · intro q
              exact Fin.elim0 q

private theorem k14t7_cover527 : ∀ P ∈ pathPatterns 2 0 [2, 1, 2, 2], HasCheckedCertificate 14 7 ([[2, 1, 2, 2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [2, 1, 2, 2] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k14t7_cover528 : ∀ P ∈ pathPatterns 3 1 [2, 1, 3], HasCheckedCertificate 14 7 ([[2, 1, 3]] ++ P) := by
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
              exact Fin.elim0 q

private theorem k14t7_cover529 : ∀ P ∈ pathPatterns 3 0 [2, 1, 4], HasCheckedCertificate 14 7 ([[2, 1, 4]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [2, 1, 4] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k14t7_cover531 : ∀ P ∈ pathPatterns 2 0 [3], HasCheckedCertificate 14 7 ([[2, 2], [3]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [3] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k14t7_cover530 : ∀ P ∈ pathPatterns 4 3 [2, 2], HasCheckedCertificate 14 7 ([[2, 2]] ++ P) := by
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
                  constructor
                  · exact by
                      intro h
                      exact False.elim ((by decide : ¬ (LexLE [2, 2] [1, 2] ∧ LexLE [1, 2] [2, 1])) h)
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
                    exact Fin.elim0 q
        · exact by
            constructor
            · exact by
                intro _
                exact k14t7_cover531
            · intro q
              exact Fin.elim0 q

private theorem k14t7_cover532 : ∀ P ∈ pathPatterns 3 1 [2, 2, 2], HasCheckedCertificate 14 7 ([[2, 2, 2]] ++ P) := by
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
              exact Fin.elim0 q

private theorem k14t7_cover533 : ∀ P ∈ pathPatterns 3 0 [2, 2, 3], HasCheckedCertificate 14 7 ([[2, 2, 3]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [2, 2, 3] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k14t7_cover534 : ∀ P ∈ pathPatterns 4 2 [2, 3], HasCheckedCertificate 14 7 ([[2, 3]] ++ P) := by
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
                    exact Fin.elim0 q
        · exact by
            constructor
            · exact by
                intro h
                exact False.elim ((by decide : ¬ (LexLE [2, 3] [2] ∧ LexLE [2] [2])) h)
            · intro q
              exact Fin.elim0 q

private theorem k14t7_cover535 : ∀ P ∈ pathPatterns 3 0 [2, 3, 2], HasCheckedCertificate 14 7 ([[2, 3, 2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [2, 3, 2] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k14t7_cover536 : ∀ P ∈ pathPatterns 4 1 [2, 4], HasCheckedCertificate 14 7 ([[2, 4]] ++ P) := by
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

private theorem k14t7_cover537 : ∀ P ∈ pathPatterns 4 0 [2, 5], HasCheckedCertificate 14 7 ([[2, 5]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [2, 5] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k14t7_seq511 : amountSequenceForall 5 5 (fun tail =>
    (LexLE [] ([2] ++ tail) ∧ LexLE ([2] ++ tail) ([2] ++ tail).reverse) →
    ∀ P ∈ pathPatterns (6 - ([2] ++ tail).length) (7 - ([2] ++ tail).sum) ([2] ++ tail),
      HasCheckedCertificate 14 7 ([] ++ (([2] ++ tail) :: P))) :=
by
  constructor
  · exact by
      intro _
      exact k14t7_cover512
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
                          constructor
                          · exact by
                              intro _
                              exact k14t7_cover523
                          · intro q
                            exact Fin.elim0 q
                · exact by
                    constructor
                    · exact by
                        intro _
                        exact k14t7_cover524
                    · intro q
                      fin_cases q
                      · exact by
                          constructor
                          · exact by
                              intro h
                              exact False.elim ((by decide : ¬ (LexLE [] [2, 1, 1, 2, 1] ∧ LexLE [2, 1, 1, 2, 1] [1, 2, 1, 1, 2])) h)
                          · intro q
                            exact Fin.elim0 q
                · exact by
                    constructor
                    · exact by
                        intro _
                        exact k14t7_cover525
                    · intro q
                      exact Fin.elim0 q
          · exact by
              constructor
              · exact by
                  intro _
                  exact k14t7_cover526
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
                            exact Fin.elim0 q
                · exact by
                    constructor
                    · exact by
                        intro _
                        exact k14t7_cover527
                    · intro q
                      exact Fin.elim0 q
          · exact by
              constructor
              · exact by
                  intro _
                  exact k14t7_cover528
              · intro q
                fin_cases q
                · exact by
                    constructor
                    · exact by
                        intro h
                        exact False.elim ((by decide : ¬ (LexLE [] [2, 1, 3, 1] ∧ LexLE [2, 1, 3, 1] [1, 3, 1, 2])) h)
                    · intro q
                      exact Fin.elim0 q
          · exact by
              constructor
              · exact by
                  intro _
                  exact k14t7_cover529
              · intro q
                exact Fin.elim0 q
    · exact by
        constructor
        · exact by
            intro _
            exact k14t7_cover530
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
                            exact Fin.elim0 q
                · exact by
                    constructor
                    · exact by
                        intro h
                        exact False.elim ((by decide : ¬ (LexLE [] [2, 2, 1, 2] ∧ LexLE [2, 2, 1, 2] [2, 1, 2, 2])) h)
                    · intro q
                      exact Fin.elim0 q
          · exact by
              constructor
              · exact by
                  intro _
                  exact k14t7_cover532
              · intro q
                fin_cases q
                · exact by
                    constructor
                    · exact by
                        intro h
                        exact False.elim ((by decide : ¬ (LexLE [] [2, 2, 2, 1] ∧ LexLE [2, 2, 2, 1] [1, 2, 2, 2])) h)
                    · intro q
                      exact Fin.elim0 q
          · exact by
              constructor
              · exact by
                  intro _
                  exact k14t7_cover533
              · intro q
                exact Fin.elim0 q
    · exact by
        constructor
        · exact by
            intro _
            exact k14t7_cover534
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
                      exact Fin.elim0 q
          · exact by
              constructor
              · exact by
                  intro _
                  exact k14t7_cover535
              · intro q
                exact Fin.elim0 q
    · exact by
        constructor
        · exact by
            intro _
            exact k14t7_cover536
        · intro q
          fin_cases q
          · exact by
              constructor
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [] [2, 4, 1] ∧ LexLE [2, 4, 1] [1, 4, 2])) h)
              · intro q
                exact Fin.elim0 q
    · exact by
        constructor
        · exact by
            intro _
            exact k14t7_cover537
        · intro q
          exact Fin.elim0 q

private theorem k14t7_cover539 : ∀ P ∈ pathPatterns 3 1 [3], HasCheckedCertificate 14 7 ([[3], [3]] ++ P) := by
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

private theorem k14t7_cover540 : ∀ P ∈ pathPatterns 3 0 [4], HasCheckedCertificate 14 7 ([[3], [4]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [4] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k14t7_cover538 : ∀ P ∈ pathPatterns 5 4 [3], HasCheckedCertificate 14 7 ([[3]] ++ P) := by
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
                        constructor
                        · exact by
                            intro h
                            exact False.elim ((by decide : ¬ (LexLE [3] [1, 1, 2] ∧ LexLE [1, 1, 2] [2, 1, 1])) h)
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
                          exact Fin.elim0 q
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
                        constructor
                        · exact by
                            intro h
                            exact False.elim ((by decide : ¬ (LexLE [3] [2, 1, 1] ∧ LexLE [2, 1, 1] [1, 1, 2])) h)
                        · intro q
                          exact Fin.elim0 q
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
                exact k14t7_cover539
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
                exact k14t7_cover540
            · intro q
              exact Fin.elim0 q

private theorem k14t7_cover541 : ∀ P ∈ pathPatterns 3 0 [3, 1, 3], HasCheckedCertificate 14 7 ([[3, 1, 3]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [3, 1, 3] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k14t7_cover542 : ∀ P ∈ pathPatterns 4 1 [3, 3], HasCheckedCertificate 14 7 ([[3, 3]] ++ P) := by
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

private theorem k14t7_cover543 : ∀ P ∈ pathPatterns 4 0 [3, 4], HasCheckedCertificate 14 7 ([[3, 4]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [3, 4] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k14t7_cover544 : ∀ P ∈ pathPatterns 5 3 [4], HasCheckedCertificate 14 7 ([[4]] ++ P) := by
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
                          exact Fin.elim0 q
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

private theorem k14t7_cover545 : ∀ P ∈ pathPatterns 5 2 [5], HasCheckedCertificate 14 7 ([[5]] ++ P) := by
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

private theorem k14t7_cover546 : ∀ P ∈ pathPatterns 5 1 [6], HasCheckedCertificate 14 7 ([[6]] ++ P) := by
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

private theorem k14t7_cover547 : ∀ P ∈ pathPatterns 5 0 [7], HasCheckedCertificate 14 7 ([[7]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [7] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k14t7_seq2 : amountSequenceForall 6 7 (fun tail =>
    (LexLE [] ([] ++ tail) ∧ LexLE ([] ++ tail) ([] ++ tail).reverse) →
    ∀ P ∈ pathPatterns (6 - ([] ++ tail).length) (7 - ([] ++ tail).sum) ([] ++ tail),
      HasCheckedCertificate 14 7 ([] ++ (([] ++ tail) :: P))) :=
by
  constructor
  · exact by
      intro _
      exact k14t7_cover3
  · intro q
    fin_cases q
    · exact k14t7_seq345

    · exact k14t7_seq511

    · exact by
        constructor
        · exact by
            intro _
            exact k14t7_cover538
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
                                  exact Fin.elim0 q
                      · exact by
                          constructor
                          · exact by
                              intro h
                              exact False.elim ((by decide : ¬ (LexLE [] [3, 1, 1, 2] ∧ LexLE [3, 1, 1, 2] [2, 1, 1, 3])) h)
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
                            exact Fin.elim0 q
                · exact by
                    constructor
                    · exact by
                        intro _
                        exact k14t7_cover541
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
                            exact Fin.elim0 q
                · exact by
                    constructor
                    · exact by
                        intro h
                        exact False.elim ((by decide : ¬ (LexLE [] [3, 2, 2] ∧ LexLE [3, 2, 2] [2, 2, 3])) h)
                    · intro q
                      exact Fin.elim0 q
          · exact by
              constructor
              · exact by
                  intro _
                  exact k14t7_cover542
              · intro q
                fin_cases q
                · exact by
                    constructor
                    · exact by
                        intro h
                        exact False.elim ((by decide : ¬ (LexLE [] [3, 3, 1] ∧ LexLE [3, 3, 1] [1, 3, 3])) h)
                    · intro q
                      exact Fin.elim0 q
          · exact by
              constructor
              · exact by
                  intro _
                  exact k14t7_cover543
              · intro q
                exact Fin.elim0 q
    · exact by
        constructor
        · exact by
            intro _
            exact k14t7_cover544
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
                            exact Fin.elim0 q
                · exact by
                    constructor
                    · exact by
                        intro h
                        exact False.elim ((by decide : ¬ (LexLE [] [4, 1, 2] ∧ LexLE [4, 1, 2] [2, 1, 4])) h)
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
                      exact Fin.elim0 q
          · exact by
              constructor
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [] [4, 3] ∧ LexLE [4, 3] [3, 4])) h)
              · intro q
                exact Fin.elim0 q
    · exact by
        constructor
        · exact by
            intro _
            exact k14t7_cover545
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
                      exact Fin.elim0 q
          · exact by
              constructor
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [] [5, 2] ∧ LexLE [5, 2] [2, 5])) h)
              · intro q
                exact Fin.elim0 q
    · exact by
        constructor
        · exact by
            intro _
            exact k14t7_cover546
        · intro q
          fin_cases q
          · exact by
              constructor
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [] [6, 1] ∧ LexLE [6, 1] [1, 6])) h)
              · intro q
                exact Fin.elim0 q
    · exact by
        constructor
        · exact by
            intro _
            exact k14t7_cover547
        · intro q
          exact Fin.elim0 q

private theorem k14t7_cover1 : ∀ P ∈ pathPatterns 7 7 [], HasCheckedCertificate 14 7 ([] ++ P) := by
  apply pathPatterns_forall_step
  exact k14t7_seq2


theorem coverage_k14_t7 :
    ∀ P ∈ pathPatterns 7 7, HasCheckedCertificate 14 7 P :=
  k14t7_cover1

private theorem k14t8_cover14 : ∀ P ∈ pathPatterns 0 6 [], HasCheckedCertificate 14 8 ([[], [], [], [], [], [], [], []] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k14t8p0, Certificates.k14t8p0_check⟩

private theorem k14t8_cover13 : ∀ P ∈ pathPatterns 1 6 [], HasCheckedCertificate 14 8 ([[], [], [], [], [], [], []] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro _
      exact k14t8_cover14

private theorem k14t8_cover15 : ∀ P ∈ pathPatterns 0 5 [1], HasCheckedCertificate 14 8 ([[], [], [], [], [], [], [1]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k14t8p1, Certificates.k14t8p1_check⟩

private theorem k14t8_cover16 : ∀ P ∈ pathPatterns 0 4 [2], HasCheckedCertificate 14 8 ([[], [], [], [], [], [], [2]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k14t8p2, Certificates.k14t8p2_check⟩

private theorem k14t8_cover17 : ∀ P ∈ pathPatterns 0 3 [3], HasCheckedCertificate 14 8 ([[], [], [], [], [], [], [3]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k14t8p3, Certificates.k14t8p3_check⟩

private theorem k14t8_cover18 : ∀ P ∈ pathPatterns 0 2 [4], HasCheckedCertificate 14 8 ([[], [], [], [], [], [], [4]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k14t8p4, Certificates.k14t8p4_check⟩

private theorem k14t8_cover19 : ∀ P ∈ pathPatterns 0 1 [5], HasCheckedCertificate 14 8 ([[], [], [], [], [], [], [5]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k14t8p5, Certificates.k14t8p5_check⟩

private theorem k14t8_cover20 : ∀ P ∈ pathPatterns 0 0 [6], HasCheckedCertificate 14 8 ([[], [], [], [], [], [], [6]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k14t8p6, Certificates.k14t8p6_check⟩

private theorem k14t8_cover12 : ∀ P ∈ pathPatterns 2 6 [], HasCheckedCertificate 14 8 ([[], [], [], [], [], []] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro _
          exact k14t8_cover13
      · intro q
        fin_cases q
        · exact by
            intro _
            exact k14t8_cover15
        · exact by
            intro _
            exact k14t8_cover16
        · exact by
            intro _
            exact k14t8_cover17
        · exact by
            intro _
            exact k14t8_cover18
        · exact by
            intro _
            exact k14t8_cover19
        · exact by
            intro _
            exact k14t8_cover20

private theorem k14t8_cover21 : ∀ P ∈ pathPatterns 1 5 [1], HasCheckedCertificate 14 8 ([[], [], [], [], [], [1]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [1] [] ∧ LexLE [] [])) h)

private theorem k14t8_cover22 : ∀ P ∈ pathPatterns 0 4 [1, 1], HasCheckedCertificate 14 8 ([[], [], [], [], [], [1, 1]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k14t8p7, Certificates.k14t8p7_check⟩

private theorem k14t8_cover23 : ∀ P ∈ pathPatterns 0 3 [1, 2], HasCheckedCertificate 14 8 ([[], [], [], [], [], [1, 2]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k14t8p8, Certificates.k14t8p8_check⟩

private theorem k14t8_cover24 : ∀ P ∈ pathPatterns 0 2 [1, 3], HasCheckedCertificate 14 8 ([[], [], [], [], [], [1, 3]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k14t8p9, Certificates.k14t8p9_check⟩

private theorem k14t8_cover25 : ∀ P ∈ pathPatterns 0 1 [1, 4], HasCheckedCertificate 14 8 ([[], [], [], [], [], [1, 4]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k14t8p10, Certificates.k14t8p10_check⟩

private theorem k14t8_cover26 : ∀ P ∈ pathPatterns 0 0 [1, 5], HasCheckedCertificate 14 8 ([[], [], [], [], [], [1, 5]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k14t8p11, Certificates.k14t8p11_check⟩

private theorem k14t8_cover27 : ∀ P ∈ pathPatterns 1 4 [2], HasCheckedCertificate 14 8 ([[], [], [], [], [], [2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [2] [] ∧ LexLE [] [])) h)

private theorem k14t8_cover28 : ∀ P ∈ pathPatterns 0 2 [2, 2], HasCheckedCertificate 14 8 ([[], [], [], [], [], [2, 2]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k14t8p12, Certificates.k14t8p12_check⟩

private theorem k14t8_cover29 : ∀ P ∈ pathPatterns 0 1 [2, 3], HasCheckedCertificate 14 8 ([[], [], [], [], [], [2, 3]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k14t8p13, Certificates.k14t8p13_check⟩

private theorem k14t8_cover30 : ∀ P ∈ pathPatterns 0 0 [2, 4], HasCheckedCertificate 14 8 ([[], [], [], [], [], [2, 4]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k14t8p14, Certificates.k14t8p14_check⟩

private theorem k14t8_cover31 : ∀ P ∈ pathPatterns 1 3 [3], HasCheckedCertificate 14 8 ([[], [], [], [], [], [3]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [3] [] ∧ LexLE [] [])) h)

private theorem k14t8_cover32 : ∀ P ∈ pathPatterns 0 0 [3, 3], HasCheckedCertificate 14 8 ([[], [], [], [], [], [3, 3]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k14t8p15, Certificates.k14t8p15_check⟩

private theorem k14t8_cover33 : ∀ P ∈ pathPatterns 1 2 [4], HasCheckedCertificate 14 8 ([[], [], [], [], [], [4]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [4] [] ∧ LexLE [] [])) h)

private theorem k14t8_cover34 : ∀ P ∈ pathPatterns 1 1 [5], HasCheckedCertificate 14 8 ([[], [], [], [], [], [5]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [5] [] ∧ LexLE [] [])) h)

private theorem k14t8_cover35 : ∀ P ∈ pathPatterns 1 0 [6], HasCheckedCertificate 14 8 ([[], [], [], [], [], [6]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [6] [] ∧ LexLE [] [])) h)

private theorem k14t8_cover11 : ∀ P ∈ pathPatterns 3 6 [], HasCheckedCertificate 14 8 ([[], [], [], [], []] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro _
          exact k14t8_cover12
      · intro q
        fin_cases q
        · exact by
            constructor
            · exact by
                intro _
                exact k14t8_cover21
            · intro q
              fin_cases q
              · exact by
                  intro _
                  exact k14t8_cover22
              · exact by
                  intro _
                  exact k14t8_cover23
              · exact by
                  intro _
                  exact k14t8_cover24
              · exact by
                  intro _
                  exact k14t8_cover25
              · exact by
                  intro _
                  exact k14t8_cover26
        · exact by
            constructor
            · exact by
                intro _
                exact k14t8_cover27
            · intro q
              fin_cases q
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [] [2, 1] ∧ LexLE [2, 1] [1, 2])) h)
              · exact by
                  intro _
                  exact k14t8_cover28
              · exact by
                  intro _
                  exact k14t8_cover29
              · exact by
                  intro _
                  exact k14t8_cover30
        · exact by
            constructor
            · exact by
                intro _
                exact k14t8_cover31
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
                  exact k14t8_cover32
        · exact by
            constructor
            · exact by
                intro _
                exact k14t8_cover33
            · intro q
              fin_cases q
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [] [4, 1] ∧ LexLE [4, 1] [1, 4])) h)
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [] [4, 2] ∧ LexLE [4, 2] [2, 4])) h)
        · exact by
            constructor
            · exact by
                intro _
                exact k14t8_cover34
            · intro q
              fin_cases q
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [] [5, 1] ∧ LexLE [5, 1] [1, 5])) h)
        · exact by
            constructor
            · exact by
                intro _
                exact k14t8_cover35
            · intro q
              exact Fin.elim0 q

private theorem k14t8_cover37 : ∀ P ∈ pathPatterns 0 4 [1], HasCheckedCertificate 14 8 ([[], [], [], [], [1], [1]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k14t8p16, Certificates.k14t8p16_check⟩

private theorem k14t8_cover38 : ∀ P ∈ pathPatterns 0 3 [2], HasCheckedCertificate 14 8 ([[], [], [], [], [1], [2]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k14t8p17, Certificates.k14t8p17_check⟩

private theorem k14t8_cover39 : ∀ P ∈ pathPatterns 0 2 [3], HasCheckedCertificate 14 8 ([[], [], [], [], [1], [3]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k14t8p18, Certificates.k14t8p18_check⟩

private theorem k14t8_cover40 : ∀ P ∈ pathPatterns 0 1 [4], HasCheckedCertificate 14 8 ([[], [], [], [], [1], [4]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k14t8p19, Certificates.k14t8p19_check⟩

private theorem k14t8_cover41 : ∀ P ∈ pathPatterns 0 0 [5], HasCheckedCertificate 14 8 ([[], [], [], [], [1], [5]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k14t8p20, Certificates.k14t8p20_check⟩

private theorem k14t8_cover36 : ∀ P ∈ pathPatterns 2 5 [1], HasCheckedCertificate 14 8 ([[], [], [], [], [1]] ++ P) := by
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
            exact k14t8_cover37
        · exact by
            intro _
            exact k14t8_cover38
        · exact by
            intro _
            exact k14t8_cover39
        · exact by
            intro _
            exact k14t8_cover40
        · exact by
            intro _
            exact k14t8_cover41

private theorem k14t8_cover42 : ∀ P ∈ pathPatterns 1 4 [1, 1], HasCheckedCertificate 14 8 ([[], [], [], [], [1, 1]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [1, 1] [] ∧ LexLE [] [])) h)

private theorem k14t8_cover43 : ∀ P ∈ pathPatterns 0 3 [1, 1, 1], HasCheckedCertificate 14 8 ([[], [], [], [], [1, 1, 1]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k14t8p21, Certificates.k14t8p21_check⟩

private theorem k14t8_cover44 : ∀ P ∈ pathPatterns 0 2 [1, 1, 2], HasCheckedCertificate 14 8 ([[], [], [], [], [1, 1, 2]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k14t8p22, Certificates.k14t8p22_check⟩

private theorem k14t8_cover45 : ∀ P ∈ pathPatterns 0 1 [1, 1, 3], HasCheckedCertificate 14 8 ([[], [], [], [], [1, 1, 3]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k14t8p23, Certificates.k14t8p23_check⟩

private theorem k14t8_cover46 : ∀ P ∈ pathPatterns 0 0 [1, 1, 4], HasCheckedCertificate 14 8 ([[], [], [], [], [1, 1, 4]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k14t8p24, Certificates.k14t8p24_check⟩

private theorem k14t8_cover47 : ∀ P ∈ pathPatterns 1 3 [1, 2], HasCheckedCertificate 14 8 ([[], [], [], [], [1, 2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [1, 2] [] ∧ LexLE [] [])) h)

private theorem k14t8_cover48 : ∀ P ∈ pathPatterns 0 2 [1, 2, 1], HasCheckedCertificate 14 8 ([[], [], [], [], [1, 2, 1]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k14t8p25, Certificates.k14t8p25_check⟩

private theorem k14t8_cover49 : ∀ P ∈ pathPatterns 0 1 [1, 2, 2], HasCheckedCertificate 14 8 ([[], [], [], [], [1, 2, 2]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k14t8p26, Certificates.k14t8p26_check⟩

private theorem k14t8_cover50 : ∀ P ∈ pathPatterns 0 0 [1, 2, 3], HasCheckedCertificate 14 8 ([[], [], [], [], [1, 2, 3]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k14t8p27, Certificates.k14t8p27_check⟩

private theorem k14t8_cover51 : ∀ P ∈ pathPatterns 1 2 [1, 3], HasCheckedCertificate 14 8 ([[], [], [], [], [1, 3]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [1, 3] [] ∧ LexLE [] [])) h)

private theorem k14t8_cover52 : ∀ P ∈ pathPatterns 0 1 [1, 3, 1], HasCheckedCertificate 14 8 ([[], [], [], [], [1, 3, 1]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k14t8p28, Certificates.k14t8p28_check⟩

private theorem k14t8_cover53 : ∀ P ∈ pathPatterns 0 0 [1, 3, 2], HasCheckedCertificate 14 8 ([[], [], [], [], [1, 3, 2]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k14t8p29, Certificates.k14t8p29_check⟩

private theorem k14t8_cover54 : ∀ P ∈ pathPatterns 1 1 [1, 4], HasCheckedCertificate 14 8 ([[], [], [], [], [1, 4]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [1, 4] [] ∧ LexLE [] [])) h)

private theorem k14t8_cover55 : ∀ P ∈ pathPatterns 0 0 [1, 4, 1], HasCheckedCertificate 14 8 ([[], [], [], [], [1, 4, 1]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k14t8p30, Certificates.k14t8p30_check⟩

private theorem k14t8_cover56 : ∀ P ∈ pathPatterns 1 0 [1, 5], HasCheckedCertificate 14 8 ([[], [], [], [], [1, 5]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [1, 5] [] ∧ LexLE [] [])) h)

private theorem k14t8_cover58 : ∀ P ∈ pathPatterns 0 2 [2], HasCheckedCertificate 14 8 ([[], [], [], [], [2], [2]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k14t8p31, Certificates.k14t8p31_check⟩

private theorem k14t8_cover59 : ∀ P ∈ pathPatterns 0 1 [3], HasCheckedCertificate 14 8 ([[], [], [], [], [2], [3]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k14t8p32, Certificates.k14t8p32_check⟩

private theorem k14t8_cover60 : ∀ P ∈ pathPatterns 0 0 [4], HasCheckedCertificate 14 8 ([[], [], [], [], [2], [4]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k14t8p33, Certificates.k14t8p33_check⟩

private theorem k14t8_cover57 : ∀ P ∈ pathPatterns 2 4 [2], HasCheckedCertificate 14 8 ([[], [], [], [], [2]] ++ P) := by
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
            exact k14t8_cover58
        · exact by
            intro _
            exact k14t8_cover59
        · exact by
            intro _
            exact k14t8_cover60

private theorem k14t8_cover61 : ∀ P ∈ pathPatterns 0 1 [2, 1, 2], HasCheckedCertificate 14 8 ([[], [], [], [], [2, 1, 2]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k14t8p34, Certificates.k14t8p34_check⟩

private theorem k14t8_cover62 : ∀ P ∈ pathPatterns 0 0 [2, 1, 3], HasCheckedCertificate 14 8 ([[], [], [], [], [2, 1, 3]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k14t8p35, Certificates.k14t8p35_check⟩

private theorem k14t8_cover63 : ∀ P ∈ pathPatterns 1 2 [2, 2], HasCheckedCertificate 14 8 ([[], [], [], [], [2, 2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [2, 2] [] ∧ LexLE [] [])) h)

private theorem k14t8_cover64 : ∀ P ∈ pathPatterns 0 0 [2, 2, 2], HasCheckedCertificate 14 8 ([[], [], [], [], [2, 2, 2]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k14t8p36, Certificates.k14t8p36_check⟩

private theorem k14t8_cover65 : ∀ P ∈ pathPatterns 1 1 [2, 3], HasCheckedCertificate 14 8 ([[], [], [], [], [2, 3]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [2, 3] [] ∧ LexLE [] [])) h)

private theorem k14t8_cover66 : ∀ P ∈ pathPatterns 1 0 [2, 4], HasCheckedCertificate 14 8 ([[], [], [], [], [2, 4]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [2, 4] [] ∧ LexLE [] [])) h)

private theorem k14t8_cover68 : ∀ P ∈ pathPatterns 0 0 [3], HasCheckedCertificate 14 8 ([[], [], [], [], [3], [3]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k14t8p37, Certificates.k14t8p37_check⟩

private theorem k14t8_cover67 : ∀ P ∈ pathPatterns 2 3 [3], HasCheckedCertificate 14 8 ([[], [], [], [], [3]] ++ P) := by
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
            exact k14t8_cover68

private theorem k14t8_cover69 : ∀ P ∈ pathPatterns 1 0 [3, 3], HasCheckedCertificate 14 8 ([[], [], [], [], [3, 3]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [3, 3] [] ∧ LexLE [] [])) h)

private theorem k14t8_cover70 : ∀ P ∈ pathPatterns 2 2 [4], HasCheckedCertificate 14 8 ([[], [], [], [], [4]] ++ P) := by
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

private theorem k14t8_cover71 : ∀ P ∈ pathPatterns 2 1 [5], HasCheckedCertificate 14 8 ([[], [], [], [], [5]] ++ P) := by
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

private theorem k14t8_cover72 : ∀ P ∈ pathPatterns 2 0 [6], HasCheckedCertificate 14 8 ([[], [], [], [], [6]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [6] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k14t8_seq10 : amountSequenceForall 3 6 (fun tail =>
    (LexLE [] ([] ++ tail) ∧ LexLE ([] ++ tail) ([] ++ tail).reverse) →
    ∀ P ∈ pathPatterns (3 - ([] ++ tail).length) (6 - ([] ++ tail).sum) ([] ++ tail),
      HasCheckedCertificate 14 8 ([[], [], [], []] ++ (([] ++ tail) :: P))) :=
by
  constructor
  · exact by
      intro _
      exact k14t8_cover11
  · intro q
    fin_cases q
    · exact by
        constructor
        · exact by
            intro _
            exact k14t8_cover36
        · intro q
          fin_cases q
          · exact by
              constructor
              · exact by
                  intro _
                  exact k14t8_cover42
              · intro q
                fin_cases q
                · exact by
                    intro _
                    exact k14t8_cover43
                · exact by
                    intro _
                    exact k14t8_cover44
                · exact by
                    intro _
                    exact k14t8_cover45
                · exact by
                    intro _
                    exact k14t8_cover46
          · exact by
              constructor
              · exact by
                  intro _
                  exact k14t8_cover47
              · intro q
                fin_cases q
                · exact by
                    intro _
                    exact k14t8_cover48
                · exact by
                    intro _
                    exact k14t8_cover49
                · exact by
                    intro _
                    exact k14t8_cover50
          · exact by
              constructor
              · exact by
                  intro _
                  exact k14t8_cover51
              · intro q
                fin_cases q
                · exact by
                    intro _
                    exact k14t8_cover52
                · exact by
                    intro _
                    exact k14t8_cover53
          · exact by
              constructor
              · exact by
                  intro _
                  exact k14t8_cover54
              · intro q
                fin_cases q
                · exact by
                    intro _
                    exact k14t8_cover55
          · exact by
              constructor
              · exact by
                  intro _
                  exact k14t8_cover56
              · intro q
                exact Fin.elim0 q
    · exact by
        constructor
        · exact by
            intro _
            exact k14t8_cover57
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
                    exact k14t8_cover61
                · exact by
                    intro _
                    exact k14t8_cover62
          · exact by
              constructor
              · exact by
                  intro _
                  exact k14t8_cover63
              · intro q
                fin_cases q
                · exact by
                    intro h
                    exact False.elim ((by decide : ¬ (LexLE [] [2, 2, 1] ∧ LexLE [2, 2, 1] [1, 2, 2])) h)
                · exact by
                    intro _
                    exact k14t8_cover64
          · exact by
              constructor
              · exact by
                  intro _
                  exact k14t8_cover65
              · intro q
                fin_cases q
                · exact by
                    intro h
                    exact False.elim ((by decide : ¬ (LexLE [] [2, 3, 1] ∧ LexLE [2, 3, 1] [1, 3, 2])) h)
          · exact by
              constructor
              · exact by
                  intro _
                  exact k14t8_cover66
              · intro q
                exact Fin.elim0 q
    · exact by
        constructor
        · exact by
            intro _
            exact k14t8_cover67
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
              constructor
              · exact by
                  intro _
                  exact k14t8_cover69
              · intro q
                exact Fin.elim0 q
    · exact by
        constructor
        · exact by
            intro _
            exact k14t8_cover70
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
              constructor
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [] [4, 2] ∧ LexLE [4, 2] [2, 4])) h)
              · intro q
                exact Fin.elim0 q
    · exact by
        constructor
        · exact by
            intro _
            exact k14t8_cover71
        · intro q
          fin_cases q
          · exact by
              constructor
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [] [5, 1] ∧ LexLE [5, 1] [1, 5])) h)
              · intro q
                exact Fin.elim0 q
    · exact by
        constructor
        · exact by
            intro _
            exact k14t8_cover72
        · intro q
          exact Fin.elim0 q

private theorem k14t8_cover9 : ∀ P ∈ pathPatterns 4 6 [], HasCheckedCertificate 14 8 ([[], [], [], []] ++ P) := by
  apply pathPatterns_forall_step
  exact k14t8_seq10


private theorem k14t8_cover75 : ∀ P ∈ pathPatterns 1 4 [1], HasCheckedCertificate 14 8 ([[], [], [], [1], [1]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [1] [] ∧ LexLE [] [])) h)

private theorem k14t8_cover76 : ∀ P ∈ pathPatterns 0 3 [1, 1], HasCheckedCertificate 14 8 ([[], [], [], [1], [1, 1]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k14t8p38, Certificates.k14t8p38_check⟩

private theorem k14t8_cover77 : ∀ P ∈ pathPatterns 0 2 [1, 2], HasCheckedCertificate 14 8 ([[], [], [], [1], [1, 2]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k14t8p39, Certificates.k14t8p39_check⟩

private theorem k14t8_cover78 : ∀ P ∈ pathPatterns 0 1 [1, 3], HasCheckedCertificate 14 8 ([[], [], [], [1], [1, 3]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k14t8p40, Certificates.k14t8p40_check⟩

private theorem k14t8_cover79 : ∀ P ∈ pathPatterns 0 0 [1, 4], HasCheckedCertificate 14 8 ([[], [], [], [1], [1, 4]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k14t8p41, Certificates.k14t8p41_check⟩

private theorem k14t8_cover80 : ∀ P ∈ pathPatterns 1 3 [2], HasCheckedCertificate 14 8 ([[], [], [], [1], [2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [2] [] ∧ LexLE [] [])) h)

private theorem k14t8_cover81 : ∀ P ∈ pathPatterns 0 1 [2, 2], HasCheckedCertificate 14 8 ([[], [], [], [1], [2, 2]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k14t8p42, Certificates.k14t8p42_check⟩

private theorem k14t8_cover82 : ∀ P ∈ pathPatterns 0 0 [2, 3], HasCheckedCertificate 14 8 ([[], [], [], [1], [2, 3]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k14t8p43, Certificates.k14t8p43_check⟩

private theorem k14t8_cover83 : ∀ P ∈ pathPatterns 1 2 [3], HasCheckedCertificate 14 8 ([[], [], [], [1], [3]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [3] [] ∧ LexLE [] [])) h)

private theorem k14t8_cover84 : ∀ P ∈ pathPatterns 1 1 [4], HasCheckedCertificate 14 8 ([[], [], [], [1], [4]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [4] [] ∧ LexLE [] [])) h)

private theorem k14t8_cover85 : ∀ P ∈ pathPatterns 1 0 [5], HasCheckedCertificate 14 8 ([[], [], [], [1], [5]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [5] [] ∧ LexLE [] [])) h)

private theorem k14t8_cover74 : ∀ P ∈ pathPatterns 3 5 [1], HasCheckedCertificate 14 8 ([[], [], [], [1]] ++ P) := by
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
                exact k14t8_cover75
            · intro q
              fin_cases q
              · exact by
                  intro _
                  exact k14t8_cover76
              · exact by
                  intro _
                  exact k14t8_cover77
              · exact by
                  intro _
                  exact k14t8_cover78
              · exact by
                  intro _
                  exact k14t8_cover79
        · exact by
            constructor
            · exact by
                intro _
                exact k14t8_cover80
            · intro q
              fin_cases q
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [1] [2, 1] ∧ LexLE [2, 1] [1, 2])) h)
              · exact by
                  intro _
                  exact k14t8_cover81
              · exact by
                  intro _
                  exact k14t8_cover82
        · exact by
            constructor
            · exact by
                intro _
                exact k14t8_cover83
            · intro q
              fin_cases q
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [1] [3, 1] ∧ LexLE [3, 1] [1, 3])) h)
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [1] [3, 2] ∧ LexLE [3, 2] [2, 3])) h)
        · exact by
            constructor
            · exact by
                intro _
                exact k14t8_cover84
            · intro q
              fin_cases q
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [1] [4, 1] ∧ LexLE [4, 1] [1, 4])) h)
        · exact by
            constructor
            · exact by
                intro _
                exact k14t8_cover85
            · intro q
              exact Fin.elim0 q

private theorem k14t8_cover87 : ∀ P ∈ pathPatterns 0 2 [2], HasCheckedCertificate 14 8 ([[], [], [], [1, 1], [2]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k14t8p44, Certificates.k14t8p44_check⟩

private theorem k14t8_cover88 : ∀ P ∈ pathPatterns 0 1 [3], HasCheckedCertificate 14 8 ([[], [], [], [1, 1], [3]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k14t8p45, Certificates.k14t8p45_check⟩

private theorem k14t8_cover89 : ∀ P ∈ pathPatterns 0 0 [4], HasCheckedCertificate 14 8 ([[], [], [], [1, 1], [4]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k14t8p46, Certificates.k14t8p46_check⟩

private theorem k14t8_cover86 : ∀ P ∈ pathPatterns 2 4 [1, 1], HasCheckedCertificate 14 8 ([[], [], [], [1, 1]] ++ P) := by
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
            exact k14t8_cover87
        · exact by
            intro _
            exact k14t8_cover88
        · exact by
            intro _
            exact k14t8_cover89

private theorem k14t8_cover90 : ∀ P ∈ pathPatterns 1 3 [1, 1, 1], HasCheckedCertificate 14 8 ([[], [], [], [1, 1, 1]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [1, 1, 1] [] ∧ LexLE [] [])) h)

private theorem k14t8_cover91 : ∀ P ∈ pathPatterns 0 2 [1, 1, 1, 1], HasCheckedCertificate 14 8 ([[], [], [], [1, 1, 1, 1]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k14t8p47, Certificates.k14t8p47_check⟩

private theorem k14t8_cover92 : ∀ P ∈ pathPatterns 0 1 [1, 1, 1, 2], HasCheckedCertificate 14 8 ([[], [], [], [1, 1, 1, 2]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k14t8p48, Certificates.k14t8p48_check⟩

private theorem k14t8_cover93 : ∀ P ∈ pathPatterns 0 0 [1, 1, 1, 3], HasCheckedCertificate 14 8 ([[], [], [], [1, 1, 1, 3]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k14t8p49, Certificates.k14t8p49_check⟩

private theorem k14t8_cover94 : ∀ P ∈ pathPatterns 1 2 [1, 1, 2], HasCheckedCertificate 14 8 ([[], [], [], [1, 1, 2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [1, 1, 2] [] ∧ LexLE [] [])) h)

private theorem k14t8_cover95 : ∀ P ∈ pathPatterns 0 1 [1, 1, 2, 1], HasCheckedCertificate 14 8 ([[], [], [], [1, 1, 2, 1]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k14t8p50, Certificates.k14t8p50_check⟩

private theorem k14t8_cover96 : ∀ P ∈ pathPatterns 0 0 [1, 1, 2, 2], HasCheckedCertificate 14 8 ([[], [], [], [1, 1, 2, 2]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k14t8p51, Certificates.k14t8p51_check⟩

private theorem k14t8_cover97 : ∀ P ∈ pathPatterns 1 1 [1, 1, 3], HasCheckedCertificate 14 8 ([[], [], [], [1, 1, 3]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [1, 1, 3] [] ∧ LexLE [] [])) h)

private theorem k14t8_cover98 : ∀ P ∈ pathPatterns 0 0 [1, 1, 3, 1], HasCheckedCertificate 14 8 ([[], [], [], [1, 1, 3, 1]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k14t8p52, Certificates.k14t8p52_check⟩

private theorem k14t8_cover99 : ∀ P ∈ pathPatterns 1 0 [1, 1, 4], HasCheckedCertificate 14 8 ([[], [], [], [1, 1, 4]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [1, 1, 4] [] ∧ LexLE [] [])) h)

private theorem k14t8_cover101 : ∀ P ∈ pathPatterns 0 1 [2], HasCheckedCertificate 14 8 ([[], [], [], [1, 2], [2]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k14t8p53, Certificates.k14t8p53_check⟩

private theorem k14t8_cover102 : ∀ P ∈ pathPatterns 0 0 [3], HasCheckedCertificate 14 8 ([[], [], [], [1, 2], [3]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k14t8p54, Certificates.k14t8p54_check⟩

private theorem k14t8_cover100 : ∀ P ∈ pathPatterns 2 3 [1, 2], HasCheckedCertificate 14 8 ([[], [], [], [1, 2]] ++ P) := by
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
            exact k14t8_cover101
        · exact by
            intro _
            exact k14t8_cover102

private theorem k14t8_cover103 : ∀ P ∈ pathPatterns 1 2 [1, 2, 1], HasCheckedCertificate 14 8 ([[], [], [], [1, 2, 1]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [1, 2, 1] [] ∧ LexLE [] [])) h)

private theorem k14t8_cover104 : ∀ P ∈ pathPatterns 0 0 [1, 2, 1, 2], HasCheckedCertificate 14 8 ([[], [], [], [1, 2, 1, 2]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k14t8p55, Certificates.k14t8p55_check⟩

private theorem k14t8_cover105 : ∀ P ∈ pathPatterns 1 1 [1, 2, 2], HasCheckedCertificate 14 8 ([[], [], [], [1, 2, 2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [1, 2, 2] [] ∧ LexLE [] [])) h)

private theorem k14t8_cover106 : ∀ P ∈ pathPatterns 0 0 [1, 2, 2, 1], HasCheckedCertificate 14 8 ([[], [], [], [1, 2, 2, 1]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k14t8p56, Certificates.k14t8p56_check⟩

private theorem k14t8_cover107 : ∀ P ∈ pathPatterns 1 0 [1, 2, 3], HasCheckedCertificate 14 8 ([[], [], [], [1, 2, 3]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [1, 2, 3] [] ∧ LexLE [] [])) h)

private theorem k14t8_cover109 : ∀ P ∈ pathPatterns 0 0 [2], HasCheckedCertificate 14 8 ([[], [], [], [1, 3], [2]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k14t8p57, Certificates.k14t8p57_check⟩

private theorem k14t8_cover108 : ∀ P ∈ pathPatterns 2 2 [1, 3], HasCheckedCertificate 14 8 ([[], [], [], [1, 3]] ++ P) := by
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
            exact k14t8_cover109

private theorem k14t8_cover110 : ∀ P ∈ pathPatterns 1 1 [1, 3, 1], HasCheckedCertificate 14 8 ([[], [], [], [1, 3, 1]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [1, 3, 1] [] ∧ LexLE [] [])) h)

private theorem k14t8_cover111 : ∀ P ∈ pathPatterns 1 0 [1, 3, 2], HasCheckedCertificate 14 8 ([[], [], [], [1, 3, 2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [1, 3, 2] [] ∧ LexLE [] [])) h)

private theorem k14t8_cover112 : ∀ P ∈ pathPatterns 2 1 [1, 4], HasCheckedCertificate 14 8 ([[], [], [], [1, 4]] ++ P) := by
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

private theorem k14t8_cover113 : ∀ P ∈ pathPatterns 1 0 [1, 4, 1], HasCheckedCertificate 14 8 ([[], [], [], [1, 4, 1]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [1, 4, 1] [] ∧ LexLE [] [])) h)

private theorem k14t8_cover114 : ∀ P ∈ pathPatterns 2 0 [1, 5], HasCheckedCertificate 14 8 ([[], [], [], [1, 5]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [1, 5] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k14t8_seq73 : amountSequenceForall 3 5 (fun tail =>
    (LexLE [] ([1] ++ tail) ∧ LexLE ([1] ++ tail) ([1] ++ tail).reverse) →
    ∀ P ∈ pathPatterns (4 - ([1] ++ tail).length) (6 - ([1] ++ tail).sum) ([1] ++ tail),
      HasCheckedCertificate 14 8 ([[], [], []] ++ (([1] ++ tail) :: P))) :=
by
  constructor
  · exact by
      intro _
      exact k14t8_cover74
  · intro q
    fin_cases q
    · exact by
        constructor
        · exact by
            intro _
            exact k14t8_cover86
        · intro q
          fin_cases q
          · exact by
              constructor
              · exact by
                  intro _
                  exact k14t8_cover90
              · intro q
                fin_cases q
                · exact by
                    intro _
                    exact k14t8_cover91
                · exact by
                    intro _
                    exact k14t8_cover92
                · exact by
                    intro _
                    exact k14t8_cover93
          · exact by
              constructor
              · exact by
                  intro _
                  exact k14t8_cover94
              · intro q
                fin_cases q
                · exact by
                    intro _
                    exact k14t8_cover95
                · exact by
                    intro _
                    exact k14t8_cover96
          · exact by
              constructor
              · exact by
                  intro _
                  exact k14t8_cover97
              · intro q
                fin_cases q
                · exact by
                    intro _
                    exact k14t8_cover98
          · exact by
              constructor
              · exact by
                  intro _
                  exact k14t8_cover99
              · intro q
                exact Fin.elim0 q
    · exact by
        constructor
        · exact by
            intro _
            exact k14t8_cover100
        · intro q
          fin_cases q
          · exact by
              constructor
              · exact by
                  intro _
                  exact k14t8_cover103
              · intro q
                fin_cases q
                · exact by
                    intro h
                    exact False.elim ((by decide : ¬ (LexLE [] [1, 2, 1, 1] ∧ LexLE [1, 2, 1, 1] [1, 1, 2, 1])) h)
                · exact by
                    intro _
                    exact k14t8_cover104
          · exact by
              constructor
              · exact by
                  intro _
                  exact k14t8_cover105
              · intro q
                fin_cases q
                · exact by
                    intro _
                    exact k14t8_cover106
          · exact by
              constructor
              · exact by
                  intro _
                  exact k14t8_cover107
              · intro q
                exact Fin.elim0 q
    · exact by
        constructor
        · exact by
            intro _
            exact k14t8_cover108
        · intro q
          fin_cases q
          · exact by
              constructor
              · exact by
                  intro _
                  exact k14t8_cover110
              · intro q
                fin_cases q
                · exact by
                    intro h
                    exact False.elim ((by decide : ¬ (LexLE [] [1, 3, 1, 1] ∧ LexLE [1, 3, 1, 1] [1, 1, 3, 1])) h)
          · exact by
              constructor
              · exact by
                  intro _
                  exact k14t8_cover111
              · intro q
                exact Fin.elim0 q
    · exact by
        constructor
        · exact by
            intro _
            exact k14t8_cover112
        · intro q
          fin_cases q
          · exact by
              constructor
              · exact by
                  intro _
                  exact k14t8_cover113
              · intro q
                exact Fin.elim0 q
    · exact by
        constructor
        · exact by
            intro _
            exact k14t8_cover114
        · intro q
          exact Fin.elim0 q

private theorem k14t8_cover116 : ∀ P ∈ pathPatterns 1 2 [2], HasCheckedCertificate 14 8 ([[], [], [], [2], [2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [2] [] ∧ LexLE [] [])) h)

private theorem k14t8_cover117 : ∀ P ∈ pathPatterns 0 0 [2, 2], HasCheckedCertificate 14 8 ([[], [], [], [2], [2, 2]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k14t8p58, Certificates.k14t8p58_check⟩

private theorem k14t8_cover118 : ∀ P ∈ pathPatterns 1 1 [3], HasCheckedCertificate 14 8 ([[], [], [], [2], [3]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [3] [] ∧ LexLE [] [])) h)

private theorem k14t8_cover119 : ∀ P ∈ pathPatterns 1 0 [4], HasCheckedCertificate 14 8 ([[], [], [], [2], [4]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [4] [] ∧ LexLE [] [])) h)

private theorem k14t8_cover115 : ∀ P ∈ pathPatterns 3 4 [2], HasCheckedCertificate 14 8 ([[], [], [], [2]] ++ P) := by
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
                exact k14t8_cover116
            · intro q
              fin_cases q
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [2] [2, 1] ∧ LexLE [2, 1] [1, 2])) h)
              · exact by
                  intro _
                  exact k14t8_cover117
        · exact by
            constructor
            · exact by
                intro _
                exact k14t8_cover118
            · intro q
              fin_cases q
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [2] [3, 1] ∧ LexLE [3, 1] [1, 3])) h)
        · exact by
            constructor
            · exact by
                intro _
                exact k14t8_cover119
            · intro q
              exact Fin.elim0 q

private theorem k14t8_cover120 : ∀ P ∈ pathPatterns 0 0 [2, 1, 1, 2], HasCheckedCertificate 14 8 ([[], [], [], [2, 1, 1, 2]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k14t8p59, Certificates.k14t8p59_check⟩

private theorem k14t8_cover121 : ∀ P ∈ pathPatterns 1 1 [2, 1, 2], HasCheckedCertificate 14 8 ([[], [], [], [2, 1, 2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [2, 1, 2] [] ∧ LexLE [] [])) h)

private theorem k14t8_cover122 : ∀ P ∈ pathPatterns 1 0 [2, 1, 3], HasCheckedCertificate 14 8 ([[], [], [], [2, 1, 3]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [2, 1, 3] [] ∧ LexLE [] [])) h)

private theorem k14t8_cover123 : ∀ P ∈ pathPatterns 2 2 [2, 2], HasCheckedCertificate 14 8 ([[], [], [], [2, 2]] ++ P) := by
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

private theorem k14t8_cover124 : ∀ P ∈ pathPatterns 1 0 [2, 2, 2], HasCheckedCertificate 14 8 ([[], [], [], [2, 2, 2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [2, 2, 2] [] ∧ LexLE [] [])) h)

private theorem k14t8_cover125 : ∀ P ∈ pathPatterns 2 1 [2, 3], HasCheckedCertificate 14 8 ([[], [], [], [2, 3]] ++ P) := by
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

private theorem k14t8_cover126 : ∀ P ∈ pathPatterns 2 0 [2, 4], HasCheckedCertificate 14 8 ([[], [], [], [2, 4]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [2, 4] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k14t8_cover128 : ∀ P ∈ pathPatterns 1 0 [3], HasCheckedCertificate 14 8 ([[], [], [], [3], [3]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [3] [] ∧ LexLE [] [])) h)

private theorem k14t8_cover127 : ∀ P ∈ pathPatterns 3 3 [3], HasCheckedCertificate 14 8 ([[], [], [], [3]] ++ P) := by
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
                exact k14t8_cover128
            · intro q
              exact Fin.elim0 q

private theorem k14t8_cover129 : ∀ P ∈ pathPatterns 2 0 [3, 3], HasCheckedCertificate 14 8 ([[], [], [], [3, 3]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [3, 3] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k14t8_cover130 : ∀ P ∈ pathPatterns 3 2 [4], HasCheckedCertificate 14 8 ([[], [], [], [4]] ++ P) := by
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

private theorem k14t8_cover131 : ∀ P ∈ pathPatterns 3 1 [5], HasCheckedCertificate 14 8 ([[], [], [], [5]] ++ P) := by
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

private theorem k14t8_cover132 : ∀ P ∈ pathPatterns 3 0 [6], HasCheckedCertificate 14 8 ([[], [], [], [6]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [6] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k14t8_seq8 : amountSequenceForall 4 6 (fun tail =>
    (LexLE [] ([] ++ tail) ∧ LexLE ([] ++ tail) ([] ++ tail).reverse) →
    ∀ P ∈ pathPatterns (4 - ([] ++ tail).length) (6 - ([] ++ tail).sum) ([] ++ tail),
      HasCheckedCertificate 14 8 ([[], [], []] ++ (([] ++ tail) :: P))) :=
by
  constructor
  · exact by
      intro _
      exact k14t8_cover9
  · intro q
    fin_cases q
    · exact k14t8_seq73

    · exact by
        constructor
        · exact by
            intro _
            exact k14t8_cover115
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
                          exact k14t8_cover120
                · exact by
                    constructor
                    · exact by
                        intro _
                        exact k14t8_cover121
                    · intro q
                      fin_cases q
                      · exact by
                          intro h
                          exact False.elim ((by decide : ¬ (LexLE [] [2, 1, 2, 1] ∧ LexLE [2, 1, 2, 1] [1, 2, 1, 2])) h)
                · exact by
                    constructor
                    · exact by
                        intro _
                        exact k14t8_cover122
                    · intro q
                      exact Fin.elim0 q
          · exact by
              constructor
              · exact by
                  intro _
                  exact k14t8_cover123
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
                    constructor
                    · exact by
                        intro _
                        exact k14t8_cover124
                    · intro q
                      exact Fin.elim0 q
          · exact by
              constructor
              · exact by
                  intro _
                  exact k14t8_cover125
              · intro q
                fin_cases q
                · exact by
                    constructor
                    · exact by
                        intro h
                        exact False.elim ((by decide : ¬ (LexLE [] [2, 3, 1] ∧ LexLE [2, 3, 1] [1, 3, 2])) h)
                    · intro q
                      exact Fin.elim0 q
          · exact by
              constructor
              · exact by
                  intro _
                  exact k14t8_cover126
              · intro q
                exact Fin.elim0 q
    · exact by
        constructor
        · exact by
            intro _
            exact k14t8_cover127
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
                    constructor
                    · exact by
                        intro h
                        exact False.elim ((by decide : ¬ (LexLE [] [3, 1, 2] ∧ LexLE [3, 1, 2] [2, 1, 3])) h)
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
                      exact Fin.elim0 q
          · exact by
              constructor
              · exact by
                  intro _
                  exact k14t8_cover129
              · intro q
                exact Fin.elim0 q
    · exact by
        constructor
        · exact by
            intro _
            exact k14t8_cover130
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
                      exact Fin.elim0 q
          · exact by
              constructor
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [] [4, 2] ∧ LexLE [4, 2] [2, 4])) h)
              · intro q
                exact Fin.elim0 q
    · exact by
        constructor
        · exact by
            intro _
            exact k14t8_cover131
        · intro q
          fin_cases q
          · exact by
              constructor
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [] [5, 1] ∧ LexLE [5, 1] [1, 5])) h)
              · intro q
                exact Fin.elim0 q
    · exact by
        constructor
        · exact by
            intro _
            exact k14t8_cover132
        · intro q
          exact Fin.elim0 q

private theorem k14t8_cover7 : ∀ P ∈ pathPatterns 5 6 [], HasCheckedCertificate 14 8 ([[], [], []] ++ P) := by
  apply pathPatterns_forall_step
  exact k14t8_seq8


private theorem k14t8_cover137 : ∀ P ∈ pathPatterns 0 3 [1], HasCheckedCertificate 14 8 ([[], [], [1], [1], [1]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k14t8p60, Certificates.k14t8p60_check⟩

private theorem k14t8_cover138 : ∀ P ∈ pathPatterns 0 2 [2], HasCheckedCertificate 14 8 ([[], [], [1], [1], [2]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k14t8p61, Certificates.k14t8p61_check⟩

private theorem k14t8_cover139 : ∀ P ∈ pathPatterns 0 1 [3], HasCheckedCertificate 14 8 ([[], [], [1], [1], [3]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k14t8p62, Certificates.k14t8p62_check⟩

private theorem k14t8_cover140 : ∀ P ∈ pathPatterns 0 0 [4], HasCheckedCertificate 14 8 ([[], [], [1], [1], [4]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k14t8p63, Certificates.k14t8p63_check⟩

private theorem k14t8_cover136 : ∀ P ∈ pathPatterns 2 4 [1], HasCheckedCertificate 14 8 ([[], [], [1], [1]] ++ P) := by
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
            exact k14t8_cover137
        · exact by
            intro _
            exact k14t8_cover138
        · exact by
            intro _
            exact k14t8_cover139
        · exact by
            intro _
            exact k14t8_cover140

private theorem k14t8_cover141 : ∀ P ∈ pathPatterns 1 3 [1, 1], HasCheckedCertificate 14 8 ([[], [], [1], [1, 1]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [1, 1] [] ∧ LexLE [] [])) h)

private theorem k14t8_cover142 : ∀ P ∈ pathPatterns 0 2 [1, 1, 1], HasCheckedCertificate 14 8 ([[], [], [1], [1, 1, 1]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k14t8p64, Certificates.k14t8p64_check⟩

private theorem k14t8_cover143 : ∀ P ∈ pathPatterns 0 1 [1, 1, 2], HasCheckedCertificate 14 8 ([[], [], [1], [1, 1, 2]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k14t8p65, Certificates.k14t8p65_check⟩

private theorem k14t8_cover144 : ∀ P ∈ pathPatterns 0 0 [1, 1, 3], HasCheckedCertificate 14 8 ([[], [], [1], [1, 1, 3]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k14t8p66, Certificates.k14t8p66_check⟩

private theorem k14t8_cover145 : ∀ P ∈ pathPatterns 1 2 [1, 2], HasCheckedCertificate 14 8 ([[], [], [1], [1, 2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [1, 2] [] ∧ LexLE [] [])) h)

private theorem k14t8_cover146 : ∀ P ∈ pathPatterns 0 1 [1, 2, 1], HasCheckedCertificate 14 8 ([[], [], [1], [1, 2, 1]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k14t8p67, Certificates.k14t8p67_check⟩

private theorem k14t8_cover147 : ∀ P ∈ pathPatterns 0 0 [1, 2, 2], HasCheckedCertificate 14 8 ([[], [], [1], [1, 2, 2]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k14t8p68, Certificates.k14t8p68_check⟩

private theorem k14t8_cover148 : ∀ P ∈ pathPatterns 1 1 [1, 3], HasCheckedCertificate 14 8 ([[], [], [1], [1, 3]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [1, 3] [] ∧ LexLE [] [])) h)

private theorem k14t8_cover149 : ∀ P ∈ pathPatterns 0 0 [1, 3, 1], HasCheckedCertificate 14 8 ([[], [], [1], [1, 3, 1]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k14t8p69, Certificates.k14t8p69_check⟩

private theorem k14t8_cover150 : ∀ P ∈ pathPatterns 1 0 [1, 4], HasCheckedCertificate 14 8 ([[], [], [1], [1, 4]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [1, 4] [] ∧ LexLE [] [])) h)

private theorem k14t8_cover152 : ∀ P ∈ pathPatterns 0 1 [2], HasCheckedCertificate 14 8 ([[], [], [1], [2], [2]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k14t8p70, Certificates.k14t8p70_check⟩

private theorem k14t8_cover153 : ∀ P ∈ pathPatterns 0 0 [3], HasCheckedCertificate 14 8 ([[], [], [1], [2], [3]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k14t8p71, Certificates.k14t8p71_check⟩

private theorem k14t8_cover151 : ∀ P ∈ pathPatterns 2 3 [2], HasCheckedCertificate 14 8 ([[], [], [1], [2]] ++ P) := by
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
            exact k14t8_cover152
        · exact by
            intro _
            exact k14t8_cover153

private theorem k14t8_cover154 : ∀ P ∈ pathPatterns 0 0 [2, 1, 2], HasCheckedCertificate 14 8 ([[], [], [1], [2, 1, 2]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k14t8p72, Certificates.k14t8p72_check⟩

private theorem k14t8_cover155 : ∀ P ∈ pathPatterns 1 1 [2, 2], HasCheckedCertificate 14 8 ([[], [], [1], [2, 2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [2, 2] [] ∧ LexLE [] [])) h)

private theorem k14t8_cover156 : ∀ P ∈ pathPatterns 1 0 [2, 3], HasCheckedCertificate 14 8 ([[], [], [1], [2, 3]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [2, 3] [] ∧ LexLE [] [])) h)

private theorem k14t8_cover157 : ∀ P ∈ pathPatterns 2 2 [3], HasCheckedCertificate 14 8 ([[], [], [1], [3]] ++ P) := by
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

private theorem k14t8_cover158 : ∀ P ∈ pathPatterns 2 1 [4], HasCheckedCertificate 14 8 ([[], [], [1], [4]] ++ P) := by
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

private theorem k14t8_cover159 : ∀ P ∈ pathPatterns 2 0 [5], HasCheckedCertificate 14 8 ([[], [], [1], [5]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [5] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k14t8_seq135 : amountSequenceForall 3 5 (fun tail =>
    (LexLE [1] ([] ++ tail) ∧ LexLE ([] ++ tail) ([] ++ tail).reverse) →
    ∀ P ∈ pathPatterns (3 - ([] ++ tail).length) (5 - ([] ++ tail).sum) ([] ++ tail),
      HasCheckedCertificate 14 8 ([[], [], [1]] ++ (([] ++ tail) :: P))) :=
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
            exact k14t8_cover136
        · intro q
          fin_cases q
          · exact by
              constructor
              · exact by
                  intro _
                  exact k14t8_cover141
              · intro q
                fin_cases q
                · exact by
                    intro _
                    exact k14t8_cover142
                · exact by
                    intro _
                    exact k14t8_cover143
                · exact by
                    intro _
                    exact k14t8_cover144
          · exact by
              constructor
              · exact by
                  intro _
                  exact k14t8_cover145
              · intro q
                fin_cases q
                · exact by
                    intro _
                    exact k14t8_cover146
                · exact by
                    intro _
                    exact k14t8_cover147
          · exact by
              constructor
              · exact by
                  intro _
                  exact k14t8_cover148
              · intro q
                fin_cases q
                · exact by
                    intro _
                    exact k14t8_cover149
          · exact by
              constructor
              · exact by
                  intro _
                  exact k14t8_cover150
              · intro q
                exact Fin.elim0 q
    · exact by
        constructor
        · exact by
            intro _
            exact k14t8_cover151
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
                    exact k14t8_cover154
          · exact by
              constructor
              · exact by
                  intro _
                  exact k14t8_cover155
              · intro q
                fin_cases q
                · exact by
                    intro h
                    exact False.elim ((by decide : ¬ (LexLE [1] [2, 2, 1] ∧ LexLE [2, 2, 1] [1, 2, 2])) h)
          · exact by
              constructor
              · exact by
                  intro _
                  exact k14t8_cover156
              · intro q
                exact Fin.elim0 q
    · exact by
        constructor
        · exact by
            intro _
            exact k14t8_cover157
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
              constructor
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [1] [3, 2] ∧ LexLE [3, 2] [2, 3])) h)
              · intro q
                exact Fin.elim0 q
    · exact by
        constructor
        · exact by
            intro _
            exact k14t8_cover158
        · intro q
          fin_cases q
          · exact by
              constructor
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [1] [4, 1] ∧ LexLE [4, 1] [1, 4])) h)
              · intro q
                exact Fin.elim0 q
    · exact by
        constructor
        · exact by
            intro _
            exact k14t8_cover159
        · intro q
          exact Fin.elim0 q

private theorem k14t8_cover134 : ∀ P ∈ pathPatterns 4 5 [1], HasCheckedCertificate 14 8 ([[], [], [1]] ++ P) := by
  apply pathPatterns_forall_step
  exact k14t8_seq135


private theorem k14t8_cover161 : ∀ P ∈ pathPatterns 0 2 [1, 1], HasCheckedCertificate 14 8 ([[], [], [1, 1], [1, 1]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k14t8p73, Certificates.k14t8p73_check⟩

private theorem k14t8_cover162 : ∀ P ∈ pathPatterns 0 1 [1, 2], HasCheckedCertificate 14 8 ([[], [], [1, 1], [1, 2]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k14t8p74, Certificates.k14t8p74_check⟩

private theorem k14t8_cover163 : ∀ P ∈ pathPatterns 0 0 [1, 3], HasCheckedCertificate 14 8 ([[], [], [1, 1], [1, 3]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k14t8p75, Certificates.k14t8p75_check⟩

private theorem k14t8_cover164 : ∀ P ∈ pathPatterns 1 2 [2], HasCheckedCertificate 14 8 ([[], [], [1, 1], [2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [2] [] ∧ LexLE [] [])) h)

private theorem k14t8_cover165 : ∀ P ∈ pathPatterns 0 0 [2, 2], HasCheckedCertificate 14 8 ([[], [], [1, 1], [2, 2]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k14t8p76, Certificates.k14t8p76_check⟩

private theorem k14t8_cover166 : ∀ P ∈ pathPatterns 1 1 [3], HasCheckedCertificate 14 8 ([[], [], [1, 1], [3]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [3] [] ∧ LexLE [] [])) h)

private theorem k14t8_cover167 : ∀ P ∈ pathPatterns 1 0 [4], HasCheckedCertificate 14 8 ([[], [], [1, 1], [4]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [4] [] ∧ LexLE [] [])) h)

private theorem k14t8_cover160 : ∀ P ∈ pathPatterns 3 4 [1, 1], HasCheckedCertificate 14 8 ([[], [], [1, 1]] ++ P) := by
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
                  exact k14t8_cover161
              · exact by
                  intro _
                  exact k14t8_cover162
              · exact by
                  intro _
                  exact k14t8_cover163
        · exact by
            constructor
            · exact by
                intro _
                exact k14t8_cover164
            · intro q
              fin_cases q
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [1, 1] [2, 1] ∧ LexLE [2, 1] [1, 2])) h)
              · exact by
                  intro _
                  exact k14t8_cover165
        · exact by
            constructor
            · exact by
                intro _
                exact k14t8_cover166
            · intro q
              fin_cases q
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [1, 1] [3, 1] ∧ LexLE [3, 1] [1, 3])) h)
        · exact by
            constructor
            · exact by
                intro _
                exact k14t8_cover167
            · intro q
              exact Fin.elim0 q

private theorem k14t8_cover169 : ∀ P ∈ pathPatterns 0 1 [2], HasCheckedCertificate 14 8 ([[], [], [1, 1, 1], [2]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k14t8p77, Certificates.k14t8p77_check⟩

private theorem k14t8_cover170 : ∀ P ∈ pathPatterns 0 0 [3], HasCheckedCertificate 14 8 ([[], [], [1, 1, 1], [3]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k14t8p78, Certificates.k14t8p78_check⟩

private theorem k14t8_cover168 : ∀ P ∈ pathPatterns 2 3 [1, 1, 1], HasCheckedCertificate 14 8 ([[], [], [1, 1, 1]] ++ P) := by
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
            exact k14t8_cover169
        · exact by
            intro _
            exact k14t8_cover170

private theorem k14t8_cover171 : ∀ P ∈ pathPatterns 1 2 [1, 1, 1, 1], HasCheckedCertificate 14 8 ([[], [], [1, 1, 1, 1]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [1, 1, 1, 1] [] ∧ LexLE [] [])) h)

private theorem k14t8_cover172 : ∀ P ∈ pathPatterns 0 1 [1, 1, 1, 1, 1], HasCheckedCertificate 14 8 ([[], [], [1, 1, 1, 1, 1]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k14t8p79, Certificates.k14t8p79_check⟩

private theorem k14t8_cover173 : ∀ P ∈ pathPatterns 0 0 [1, 1, 1, 1, 2], HasCheckedCertificate 14 8 ([[], [], [1, 1, 1, 1, 2]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k14t8p80, Certificates.k14t8p80_check⟩

private theorem k14t8_cover174 : ∀ P ∈ pathPatterns 1 1 [1, 1, 1, 2], HasCheckedCertificate 14 8 ([[], [], [1, 1, 1, 2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [1, 1, 1, 2] [] ∧ LexLE [] [])) h)

private theorem k14t8_cover175 : ∀ P ∈ pathPatterns 0 0 [1, 1, 1, 2, 1], HasCheckedCertificate 14 8 ([[], [], [1, 1, 1, 2, 1]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k14t8p81, Certificates.k14t8p81_check⟩

private theorem k14t8_cover176 : ∀ P ∈ pathPatterns 1 0 [1, 1, 1, 3], HasCheckedCertificate 14 8 ([[], [], [1, 1, 1, 3]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [1, 1, 1, 3] [] ∧ LexLE [] [])) h)

private theorem k14t8_cover178 : ∀ P ∈ pathPatterns 0 0 [2], HasCheckedCertificate 14 8 ([[], [], [1, 1, 2], [2]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k14t8p82, Certificates.k14t8p82_check⟩

private theorem k14t8_cover177 : ∀ P ∈ pathPatterns 2 2 [1, 1, 2], HasCheckedCertificate 14 8 ([[], [], [1, 1, 2]] ++ P) := by
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
            exact k14t8_cover178

private theorem k14t8_cover179 : ∀ P ∈ pathPatterns 1 1 [1, 1, 2, 1], HasCheckedCertificate 14 8 ([[], [], [1, 1, 2, 1]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [1, 1, 2, 1] [] ∧ LexLE [] [])) h)

private theorem k14t8_cover180 : ∀ P ∈ pathPatterns 0 0 [1, 1, 2, 1, 1], HasCheckedCertificate 14 8 ([[], [], [1, 1, 2, 1, 1]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k14t8p83, Certificates.k14t8p83_check⟩

private theorem k14t8_cover181 : ∀ P ∈ pathPatterns 1 0 [1, 1, 2, 2], HasCheckedCertificate 14 8 ([[], [], [1, 1, 2, 2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [1, 1, 2, 2] [] ∧ LexLE [] [])) h)

private theorem k14t8_cover182 : ∀ P ∈ pathPatterns 2 1 [1, 1, 3], HasCheckedCertificate 14 8 ([[], [], [1, 1, 3]] ++ P) := by
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

private theorem k14t8_cover183 : ∀ P ∈ pathPatterns 1 0 [1, 1, 3, 1], HasCheckedCertificate 14 8 ([[], [], [1, 1, 3, 1]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [1, 1, 3, 1] [] ∧ LexLE [] [])) h)

private theorem k14t8_cover184 : ∀ P ∈ pathPatterns 2 0 [1, 1, 4], HasCheckedCertificate 14 8 ([[], [], [1, 1, 4]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [1, 1, 4] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k14t8_cover186 : ∀ P ∈ pathPatterns 0 0 [1, 2], HasCheckedCertificate 14 8 ([[], [], [1, 2], [1, 2]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k14t8p84, Certificates.k14t8p84_check⟩

private theorem k14t8_cover187 : ∀ P ∈ pathPatterns 1 1 [2], HasCheckedCertificate 14 8 ([[], [], [1, 2], [2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [2] [] ∧ LexLE [] [])) h)

private theorem k14t8_cover188 : ∀ P ∈ pathPatterns 1 0 [3], HasCheckedCertificate 14 8 ([[], [], [1, 2], [3]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [3] [] ∧ LexLE [] [])) h)

private theorem k14t8_cover185 : ∀ P ∈ pathPatterns 3 3 [1, 2], HasCheckedCertificate 14 8 ([[], [], [1, 2]] ++ P) := by
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
                  exact k14t8_cover186
        · exact by
            constructor
            · exact by
                intro _
                exact k14t8_cover187
            · intro q
              fin_cases q
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [1, 2] [2, 1] ∧ LexLE [2, 1] [1, 2])) h)
        · exact by
            constructor
            · exact by
                intro _
                exact k14t8_cover188
            · intro q
              exact Fin.elim0 q

private theorem k14t8_cover190 : ∀ P ∈ pathPatterns 0 0 [2], HasCheckedCertificate 14 8 ([[], [], [1, 2, 1], [2]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k14t8p85, Certificates.k14t8p85_check⟩

private theorem k14t8_cover189 : ∀ P ∈ pathPatterns 2 2 [1, 2, 1], HasCheckedCertificate 14 8 ([[], [], [1, 2, 1]] ++ P) := by
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
            exact k14t8_cover190

private theorem k14t8_cover191 : ∀ P ∈ pathPatterns 1 0 [1, 2, 1, 2], HasCheckedCertificate 14 8 ([[], [], [1, 2, 1, 2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [1, 2, 1, 2] [] ∧ LexLE [] [])) h)

private theorem k14t8_cover192 : ∀ P ∈ pathPatterns 2 1 [1, 2, 2], HasCheckedCertificate 14 8 ([[], [], [1, 2, 2]] ++ P) := by
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

private theorem k14t8_cover193 : ∀ P ∈ pathPatterns 1 0 [1, 2, 2, 1], HasCheckedCertificate 14 8 ([[], [], [1, 2, 2, 1]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [1, 2, 2, 1] [] ∧ LexLE [] [])) h)

private theorem k14t8_cover194 : ∀ P ∈ pathPatterns 2 0 [1, 2, 3], HasCheckedCertificate 14 8 ([[], [], [1, 2, 3]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [1, 2, 3] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k14t8_cover196 : ∀ P ∈ pathPatterns 1 0 [2], HasCheckedCertificate 14 8 ([[], [], [1, 3], [2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [2] [] ∧ LexLE [] [])) h)

private theorem k14t8_cover195 : ∀ P ∈ pathPatterns 3 2 [1, 3], HasCheckedCertificate 14 8 ([[], [], [1, 3]] ++ P) := by
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
            constructor
            · exact by
                intro _
                exact k14t8_cover196
            · intro q
              exact Fin.elim0 q

private theorem k14t8_cover197 : ∀ P ∈ pathPatterns 2 1 [1, 3, 1], HasCheckedCertificate 14 8 ([[], [], [1, 3, 1]] ++ P) := by
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

private theorem k14t8_cover198 : ∀ P ∈ pathPatterns 2 0 [1, 3, 2], HasCheckedCertificate 14 8 ([[], [], [1, 3, 2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [1, 3, 2] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k14t8_cover199 : ∀ P ∈ pathPatterns 3 1 [1, 4], HasCheckedCertificate 14 8 ([[], [], [1, 4]] ++ P) := by
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
              exact Fin.elim0 q

private theorem k14t8_cover200 : ∀ P ∈ pathPatterns 2 0 [1, 4, 1], HasCheckedCertificate 14 8 ([[], [], [1, 4, 1]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [1, 4, 1] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k14t8_cover201 : ∀ P ∈ pathPatterns 3 0 [1, 5], HasCheckedCertificate 14 8 ([[], [], [1, 5]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [1, 5] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k14t8_seq133 : amountSequenceForall 4 5 (fun tail =>
    (LexLE [] ([1] ++ tail) ∧ LexLE ([1] ++ tail) ([1] ++ tail).reverse) →
    ∀ P ∈ pathPatterns (5 - ([1] ++ tail).length) (6 - ([1] ++ tail).sum) ([1] ++ tail),
      HasCheckedCertificate 14 8 ([[], []] ++ (([1] ++ tail) :: P))) :=
by
  constructor
  · exact by
      intro _
      exact k14t8_cover134
  · intro q
    fin_cases q
    · exact by
        constructor
        · exact by
            intro _
            exact k14t8_cover160
        · intro q
          fin_cases q
          · exact by
              constructor
              · exact by
                  intro _
                  exact k14t8_cover168
              · intro q
                fin_cases q
                · exact by
                    constructor
                    · exact by
                        intro _
                        exact k14t8_cover171
                    · intro q
                      fin_cases q
                      · exact by
                          intro _
                          exact k14t8_cover172
                      · exact by
                          intro _
                          exact k14t8_cover173
                · exact by
                    constructor
                    · exact by
                        intro _
                        exact k14t8_cover174
                    · intro q
                      fin_cases q
                      · exact by
                          intro _
                          exact k14t8_cover175
                · exact by
                    constructor
                    · exact by
                        intro _
                        exact k14t8_cover176
                    · intro q
                      exact Fin.elim0 q
          · exact by
              constructor
              · exact by
                  intro _
                  exact k14t8_cover177
              · intro q
                fin_cases q
                · exact by
                    constructor
                    · exact by
                        intro _
                        exact k14t8_cover179
                    · intro q
                      fin_cases q
                      · exact by
                          intro _
                          exact k14t8_cover180
                · exact by
                    constructor
                    · exact by
                        intro _
                        exact k14t8_cover181
                    · intro q
                      exact Fin.elim0 q
          · exact by
              constructor
              · exact by
                  intro _
                  exact k14t8_cover182
              · intro q
                fin_cases q
                · exact by
                    constructor
                    · exact by
                        intro _
                        exact k14t8_cover183
                    · intro q
                      exact Fin.elim0 q
          · exact by
              constructor
              · exact by
                  intro _
                  exact k14t8_cover184
              · intro q
                exact Fin.elim0 q
    · exact by
        constructor
        · exact by
            intro _
            exact k14t8_cover185
        · intro q
          fin_cases q
          · exact by
              constructor
              · exact by
                  intro _
                  exact k14t8_cover189
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
                    constructor
                    · exact by
                        intro _
                        exact k14t8_cover191
                    · intro q
                      exact Fin.elim0 q
          · exact by
              constructor
              · exact by
                  intro _
                  exact k14t8_cover192
              · intro q
                fin_cases q
                · exact by
                    constructor
                    · exact by
                        intro _
                        exact k14t8_cover193
                    · intro q
                      exact Fin.elim0 q
          · exact by
              constructor
              · exact by
                  intro _
                  exact k14t8_cover194
              · intro q
                exact Fin.elim0 q
    · exact by
        constructor
        · exact by
            intro _
            exact k14t8_cover195
        · intro q
          fin_cases q
          · exact by
              constructor
              · exact by
                  intro _
                  exact k14t8_cover197
              · intro q
                fin_cases q
                · exact by
                    constructor
                    · exact by
                        intro h
                        exact False.elim ((by decide : ¬ (LexLE [] [1, 3, 1, 1] ∧ LexLE [1, 3, 1, 1] [1, 1, 3, 1])) h)
                    · intro q
                      exact Fin.elim0 q
          · exact by
              constructor
              · exact by
                  intro _
                  exact k14t8_cover198
              · intro q
                exact Fin.elim0 q
    · exact by
        constructor
        · exact by
            intro _
            exact k14t8_cover199
        · intro q
          fin_cases q
          · exact by
              constructor
              · exact by
                  intro _
                  exact k14t8_cover200
              · intro q
                exact Fin.elim0 q
    · exact by
        constructor
        · exact by
            intro _
            exact k14t8_cover201
        · intro q
          exact Fin.elim0 q

private theorem k14t8_cover204 : ∀ P ∈ pathPatterns 0 0 [2], HasCheckedCertificate 14 8 ([[], [], [2], [2], [2]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k14t8p86, Certificates.k14t8p86_check⟩

private theorem k14t8_cover203 : ∀ P ∈ pathPatterns 2 2 [2], HasCheckedCertificate 14 8 ([[], [], [2], [2]] ++ P) := by
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
            exact k14t8_cover204

private theorem k14t8_cover205 : ∀ P ∈ pathPatterns 1 0 [2, 2], HasCheckedCertificate 14 8 ([[], [], [2], [2, 2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [2, 2] [] ∧ LexLE [] [])) h)

private theorem k14t8_cover206 : ∀ P ∈ pathPatterns 2 1 [3], HasCheckedCertificate 14 8 ([[], [], [2], [3]] ++ P) := by
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

private theorem k14t8_cover207 : ∀ P ∈ pathPatterns 2 0 [4], HasCheckedCertificate 14 8 ([[], [], [2], [4]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [4] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k14t8_cover202 : ∀ P ∈ pathPatterns 4 4 [2], HasCheckedCertificate 14 8 ([[], [], [2]] ++ P) := by
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
                exact k14t8_cover203
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
                      exact k14t8_cover205
                  · intro q
                    exact Fin.elim0 q
        · exact by
            constructor
            · exact by
                intro _
                exact k14t8_cover206
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
                exact k14t8_cover207
            · intro q
              exact Fin.elim0 q

private theorem k14t8_cover208 : ∀ P ∈ pathPatterns 1 0 [2, 1, 1, 2], HasCheckedCertificate 14 8 ([[], [], [2, 1, 1, 2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [2, 1, 1, 2] [] ∧ LexLE [] [])) h)

private theorem k14t8_cover209 : ∀ P ∈ pathPatterns 2 1 [2, 1, 2], HasCheckedCertificate 14 8 ([[], [], [2, 1, 2]] ++ P) := by
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

private theorem k14t8_cover210 : ∀ P ∈ pathPatterns 2 0 [2, 1, 3], HasCheckedCertificate 14 8 ([[], [], [2, 1, 3]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [2, 1, 3] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k14t8_cover211 : ∀ P ∈ pathPatterns 3 2 [2, 2], HasCheckedCertificate 14 8 ([[], [], [2, 2]] ++ P) := by
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

private theorem k14t8_cover212 : ∀ P ∈ pathPatterns 2 0 [2, 2, 2], HasCheckedCertificate 14 8 ([[], [], [2, 2, 2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [2, 2, 2] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k14t8_cover213 : ∀ P ∈ pathPatterns 3 1 [2, 3], HasCheckedCertificate 14 8 ([[], [], [2, 3]] ++ P) := by
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

private theorem k14t8_cover214 : ∀ P ∈ pathPatterns 3 0 [2, 4], HasCheckedCertificate 14 8 ([[], [], [2, 4]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [2, 4] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k14t8_cover216 : ∀ P ∈ pathPatterns 2 0 [3], HasCheckedCertificate 14 8 ([[], [], [3], [3]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [3] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k14t8_cover215 : ∀ P ∈ pathPatterns 4 3 [3], HasCheckedCertificate 14 8 ([[], [], [3]] ++ P) := by
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
                exact k14t8_cover216
            · intro q
              exact Fin.elim0 q

private theorem k14t8_cover217 : ∀ P ∈ pathPatterns 3 0 [3, 3], HasCheckedCertificate 14 8 ([[], [], [3, 3]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [3, 3] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k14t8_cover218 : ∀ P ∈ pathPatterns 4 2 [4], HasCheckedCertificate 14 8 ([[], [], [4]] ++ P) := by
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

private theorem k14t8_cover219 : ∀ P ∈ pathPatterns 4 1 [5], HasCheckedCertificate 14 8 ([[], [], [5]] ++ P) := by
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

private theorem k14t8_cover220 : ∀ P ∈ pathPatterns 4 0 [6], HasCheckedCertificate 14 8 ([[], [], [6]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [6] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k14t8_seq6 : amountSequenceForall 5 6 (fun tail =>
    (LexLE [] ([] ++ tail) ∧ LexLE ([] ++ tail) ([] ++ tail).reverse) →
    ∀ P ∈ pathPatterns (5 - ([] ++ tail).length) (6 - ([] ++ tail).sum) ([] ++ tail),
      HasCheckedCertificate 14 8 ([[], []] ++ (([] ++ tail) :: P))) :=
by
  constructor
  · exact by
      intro _
      exact k14t8_cover7
  · intro q
    fin_cases q
    · exact k14t8_seq133

    · exact by
        constructor
        · exact by
            intro _
            exact k14t8_cover202
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
                          constructor
                          · exact by
                              intro _
                              exact k14t8_cover208
                          · intro q
                            exact Fin.elim0 q
                · exact by
                    constructor
                    · exact by
                        intro _
                        exact k14t8_cover209
                    · intro q
                      fin_cases q
                      · exact by
                          constructor
                          · exact by
                              intro h
                              exact False.elim ((by decide : ¬ (LexLE [] [2, 1, 2, 1] ∧ LexLE [2, 1, 2, 1] [1, 2, 1, 2])) h)
                          · intro q
                            exact Fin.elim0 q
                · exact by
                    constructor
                    · exact by
                        intro _
                        exact k14t8_cover210
                    · intro q
                      exact Fin.elim0 q
          · exact by
              constructor
              · exact by
                  intro _
                  exact k14t8_cover211
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
                            exact Fin.elim0 q
                · exact by
                    constructor
                    · exact by
                        intro _
                        exact k14t8_cover212
                    · intro q
                      exact Fin.elim0 q
          · exact by
              constructor
              · exact by
                  intro _
                  exact k14t8_cover213
              · intro q
                fin_cases q
                · exact by
                    constructor
                    · exact by
                        intro h
                        exact False.elim ((by decide : ¬ (LexLE [] [2, 3, 1] ∧ LexLE [2, 3, 1] [1, 3, 2])) h)
                    · intro q
                      exact Fin.elim0 q
          · exact by
              constructor
              · exact by
                  intro _
                  exact k14t8_cover214
              · intro q
                exact Fin.elim0 q
    · exact by
        constructor
        · exact by
            intro _
            exact k14t8_cover215
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
                            exact Fin.elim0 q
                · exact by
                    constructor
                    · exact by
                        intro h
                        exact False.elim ((by decide : ¬ (LexLE [] [3, 1, 2] ∧ LexLE [3, 1, 2] [2, 1, 3])) h)
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
                      exact Fin.elim0 q
          · exact by
              constructor
              · exact by
                  intro _
                  exact k14t8_cover217
              · intro q
                exact Fin.elim0 q
    · exact by
        constructor
        · exact by
            intro _
            exact k14t8_cover218
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
                      exact Fin.elim0 q
          · exact by
              constructor
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [] [4, 2] ∧ LexLE [4, 2] [2, 4])) h)
              · intro q
                exact Fin.elim0 q
    · exact by
        constructor
        · exact by
            intro _
            exact k14t8_cover219
        · intro q
          fin_cases q
          · exact by
              constructor
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [] [5, 1] ∧ LexLE [5, 1] [1, 5])) h)
              · intro q
                exact Fin.elim0 q
    · exact by
        constructor
        · exact by
            intro _
            exact k14t8_cover220
        · intro q
          exact Fin.elim0 q

private theorem k14t8_cover5 : ∀ P ∈ pathPatterns 6 6 [], HasCheckedCertificate 14 8 ([[], []] ++ P) := by
  apply pathPatterns_forall_step
  exact k14t8_seq6


private theorem k14t8_cover225 : ∀ P ∈ pathPatterns 1 3 [1], HasCheckedCertificate 14 8 ([[], [1], [1], [1]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [1] [] ∧ LexLE [] [])) h)

private theorem k14t8_cover226 : ∀ P ∈ pathPatterns 0 2 [1, 1], HasCheckedCertificate 14 8 ([[], [1], [1], [1, 1]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k14t8p87, Certificates.k14t8p87_check⟩

private theorem k14t8_cover227 : ∀ P ∈ pathPatterns 0 1 [1, 2], HasCheckedCertificate 14 8 ([[], [1], [1], [1, 2]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k14t8p88, Certificates.k14t8p88_check⟩

private theorem k14t8_cover228 : ∀ P ∈ pathPatterns 0 0 [1, 3], HasCheckedCertificate 14 8 ([[], [1], [1], [1, 3]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k14t8p89, Certificates.k14t8p89_check⟩

private theorem k14t8_cover229 : ∀ P ∈ pathPatterns 1 2 [2], HasCheckedCertificate 14 8 ([[], [1], [1], [2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [2] [] ∧ LexLE [] [])) h)

private theorem k14t8_cover230 : ∀ P ∈ pathPatterns 0 0 [2, 2], HasCheckedCertificate 14 8 ([[], [1], [1], [2, 2]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k14t8p90, Certificates.k14t8p90_check⟩

private theorem k14t8_cover231 : ∀ P ∈ pathPatterns 1 1 [3], HasCheckedCertificate 14 8 ([[], [1], [1], [3]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [3] [] ∧ LexLE [] [])) h)

private theorem k14t8_cover232 : ∀ P ∈ pathPatterns 1 0 [4], HasCheckedCertificate 14 8 ([[], [1], [1], [4]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [4] [] ∧ LexLE [] [])) h)

private theorem k14t8_cover224 : ∀ P ∈ pathPatterns 3 4 [1], HasCheckedCertificate 14 8 ([[], [1], [1]] ++ P) := by
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
                exact k14t8_cover225
            · intro q
              fin_cases q
              · exact by
                  intro _
                  exact k14t8_cover226
              · exact by
                  intro _
                  exact k14t8_cover227
              · exact by
                  intro _
                  exact k14t8_cover228
        · exact by
            constructor
            · exact by
                intro _
                exact k14t8_cover229
            · intro q
              fin_cases q
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [1] [2, 1] ∧ LexLE [2, 1] [1, 2])) h)
              · exact by
                  intro _
                  exact k14t8_cover230
        · exact by
            constructor
            · exact by
                intro _
                exact k14t8_cover231
            · intro q
              fin_cases q
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [1] [3, 1] ∧ LexLE [3, 1] [1, 3])) h)
        · exact by
            constructor
            · exact by
                intro _
                exact k14t8_cover232
            · intro q
              exact Fin.elim0 q

private theorem k14t8_cover234 : ∀ P ∈ pathPatterns 0 1 [2], HasCheckedCertificate 14 8 ([[], [1], [1, 1], [2]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k14t8p91, Certificates.k14t8p91_check⟩

private theorem k14t8_cover235 : ∀ P ∈ pathPatterns 0 0 [3], HasCheckedCertificate 14 8 ([[], [1], [1, 1], [3]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k14t8p92, Certificates.k14t8p92_check⟩

private theorem k14t8_cover233 : ∀ P ∈ pathPatterns 2 3 [1, 1], HasCheckedCertificate 14 8 ([[], [1], [1, 1]] ++ P) := by
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
            exact k14t8_cover234
        · exact by
            intro _
            exact k14t8_cover235

private theorem k14t8_cover236 : ∀ P ∈ pathPatterns 1 2 [1, 1, 1], HasCheckedCertificate 14 8 ([[], [1], [1, 1, 1]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [1, 1, 1] [] ∧ LexLE [] [])) h)

private theorem k14t8_cover237 : ∀ P ∈ pathPatterns 0 1 [1, 1, 1, 1], HasCheckedCertificate 14 8 ([[], [1], [1, 1, 1, 1]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k14t8p93, Certificates.k14t8p93_check⟩

private theorem k14t8_cover238 : ∀ P ∈ pathPatterns 0 0 [1, 1, 1, 2], HasCheckedCertificate 14 8 ([[], [1], [1, 1, 1, 2]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k14t8p94, Certificates.k14t8p94_check⟩

private theorem k14t8_cover239 : ∀ P ∈ pathPatterns 1 1 [1, 1, 2], HasCheckedCertificate 14 8 ([[], [1], [1, 1, 2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [1, 1, 2] [] ∧ LexLE [] [])) h)

private theorem k14t8_cover240 : ∀ P ∈ pathPatterns 0 0 [1, 1, 2, 1], HasCheckedCertificate 14 8 ([[], [1], [1, 1, 2, 1]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k14t8p95, Certificates.k14t8p95_check⟩

private theorem k14t8_cover241 : ∀ P ∈ pathPatterns 1 0 [1, 1, 3], HasCheckedCertificate 14 8 ([[], [1], [1, 1, 3]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [1, 1, 3] [] ∧ LexLE [] [])) h)

private theorem k14t8_cover243 : ∀ P ∈ pathPatterns 0 0 [2], HasCheckedCertificate 14 8 ([[], [1], [1, 2], [2]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k14t8p96, Certificates.k14t8p96_check⟩

private theorem k14t8_cover242 : ∀ P ∈ pathPatterns 2 2 [1, 2], HasCheckedCertificate 14 8 ([[], [1], [1, 2]] ++ P) := by
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
            exact k14t8_cover243

private theorem k14t8_cover244 : ∀ P ∈ pathPatterns 1 1 [1, 2, 1], HasCheckedCertificate 14 8 ([[], [1], [1, 2, 1]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [1, 2, 1] [] ∧ LexLE [] [])) h)

private theorem k14t8_cover245 : ∀ P ∈ pathPatterns 1 0 [1, 2, 2], HasCheckedCertificate 14 8 ([[], [1], [1, 2, 2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [1, 2, 2] [] ∧ LexLE [] [])) h)

private theorem k14t8_cover246 : ∀ P ∈ pathPatterns 2 1 [1, 3], HasCheckedCertificate 14 8 ([[], [1], [1, 3]] ++ P) := by
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

private theorem k14t8_cover247 : ∀ P ∈ pathPatterns 1 0 [1, 3, 1], HasCheckedCertificate 14 8 ([[], [1], [1, 3, 1]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [1, 3, 1] [] ∧ LexLE [] [])) h)

private theorem k14t8_cover248 : ∀ P ∈ pathPatterns 2 0 [1, 4], HasCheckedCertificate 14 8 ([[], [1], [1, 4]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [1, 4] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k14t8_cover250 : ∀ P ∈ pathPatterns 1 1 [2], HasCheckedCertificate 14 8 ([[], [1], [2], [2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [2] [] ∧ LexLE [] [])) h)

private theorem k14t8_cover251 : ∀ P ∈ pathPatterns 1 0 [3], HasCheckedCertificate 14 8 ([[], [1], [2], [3]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [3] [] ∧ LexLE [] [])) h)

private theorem k14t8_cover249 : ∀ P ∈ pathPatterns 3 3 [2], HasCheckedCertificate 14 8 ([[], [1], [2]] ++ P) := by
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
                exact k14t8_cover250
            · intro q
              fin_cases q
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [2] [2, 1] ∧ LexLE [2, 1] [1, 2])) h)
        · exact by
            constructor
            · exact by
                intro _
                exact k14t8_cover251
            · intro q
              exact Fin.elim0 q

private theorem k14t8_cover252 : ∀ P ∈ pathPatterns 1 0 [2, 1, 2], HasCheckedCertificate 14 8 ([[], [1], [2, 1, 2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [2, 1, 2] [] ∧ LexLE [] [])) h)

private theorem k14t8_cover253 : ∀ P ∈ pathPatterns 2 1 [2, 2], HasCheckedCertificate 14 8 ([[], [1], [2, 2]] ++ P) := by
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

private theorem k14t8_cover254 : ∀ P ∈ pathPatterns 2 0 [2, 3], HasCheckedCertificate 14 8 ([[], [1], [2, 3]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [2, 3] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k14t8_cover255 : ∀ P ∈ pathPatterns 3 2 [3], HasCheckedCertificate 14 8 ([[], [1], [3]] ++ P) := by
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

private theorem k14t8_cover256 : ∀ P ∈ pathPatterns 3 1 [4], HasCheckedCertificate 14 8 ([[], [1], [4]] ++ P) := by
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

private theorem k14t8_cover257 : ∀ P ∈ pathPatterns 3 0 [5], HasCheckedCertificate 14 8 ([[], [1], [5]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [5] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k14t8_seq223 : amountSequenceForall 4 5 (fun tail =>
    (LexLE [1] ([] ++ tail) ∧ LexLE ([] ++ tail) ([] ++ tail).reverse) →
    ∀ P ∈ pathPatterns (4 - ([] ++ tail).length) (5 - ([] ++ tail).sum) ([] ++ tail),
      HasCheckedCertificate 14 8 ([[], [1]] ++ (([] ++ tail) :: P))) :=
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
            exact k14t8_cover224
        · intro q
          fin_cases q
          · exact by
              constructor
              · exact by
                  intro _
                  exact k14t8_cover233
              · intro q
                fin_cases q
                · exact by
                    constructor
                    · exact by
                        intro _
                        exact k14t8_cover236
                    · intro q
                      fin_cases q
                      · exact by
                          intro _
                          exact k14t8_cover237
                      · exact by
                          intro _
                          exact k14t8_cover238
                · exact by
                    constructor
                    · exact by
                        intro _
                        exact k14t8_cover239
                    · intro q
                      fin_cases q
                      · exact by
                          intro _
                          exact k14t8_cover240
                · exact by
                    constructor
                    · exact by
                        intro _
                        exact k14t8_cover241
                    · intro q
                      exact Fin.elim0 q
          · exact by
              constructor
              · exact by
                  intro _
                  exact k14t8_cover242
              · intro q
                fin_cases q
                · exact by
                    constructor
                    · exact by
                        intro _
                        exact k14t8_cover244
                    · intro q
                      fin_cases q
                      · exact by
                          intro h
                          exact False.elim ((by decide : ¬ (LexLE [1] [1, 2, 1, 1] ∧ LexLE [1, 2, 1, 1] [1, 1, 2, 1])) h)
                · exact by
                    constructor
                    · exact by
                        intro _
                        exact k14t8_cover245
                    · intro q
                      exact Fin.elim0 q
          · exact by
              constructor
              · exact by
                  intro _
                  exact k14t8_cover246
              · intro q
                fin_cases q
                · exact by
                    constructor
                    · exact by
                        intro _
                        exact k14t8_cover247
                    · intro q
                      exact Fin.elim0 q
          · exact by
              constructor
              · exact by
                  intro _
                  exact k14t8_cover248
              · intro q
                exact Fin.elim0 q
    · exact by
        constructor
        · exact by
            intro _
            exact k14t8_cover249
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
                    constructor
                    · exact by
                        intro _
                        exact k14t8_cover252
                    · intro q
                      exact Fin.elim0 q
          · exact by
              constructor
              · exact by
                  intro _
                  exact k14t8_cover253
              · intro q
                fin_cases q
                · exact by
                    constructor
                    · exact by
                        intro h
                        exact False.elim ((by decide : ¬ (LexLE [1] [2, 2, 1] ∧ LexLE [2, 2, 1] [1, 2, 2])) h)
                    · intro q
                      exact Fin.elim0 q
          · exact by
              constructor
              · exact by
                  intro _
                  exact k14t8_cover254
              · intro q
                exact Fin.elim0 q
    · exact by
        constructor
        · exact by
            intro _
            exact k14t8_cover255
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
                      exact Fin.elim0 q
          · exact by
              constructor
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [1] [3, 2] ∧ LexLE [3, 2] [2, 3])) h)
              · intro q
                exact Fin.elim0 q
    · exact by
        constructor
        · exact by
            intro _
            exact k14t8_cover256
        · intro q
          fin_cases q
          · exact by
              constructor
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [1] [4, 1] ∧ LexLE [4, 1] [1, 4])) h)
              · intro q
                exact Fin.elim0 q
    · exact by
        constructor
        · exact by
            intro _
            exact k14t8_cover257
        · intro q
          exact Fin.elim0 q

private theorem k14t8_cover222 : ∀ P ∈ pathPatterns 5 5 [1], HasCheckedCertificate 14 8 ([[], [1]] ++ P) := by
  apply pathPatterns_forall_step
  exact k14t8_seq223


private theorem k14t8_cover259 : ∀ P ∈ pathPatterns 1 2 [1, 1], HasCheckedCertificate 14 8 ([[], [1, 1], [1, 1]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [1, 1] [] ∧ LexLE [] [])) h)

private theorem k14t8_cover260 : ∀ P ∈ pathPatterns 0 1 [1, 1, 1], HasCheckedCertificate 14 8 ([[], [1, 1], [1, 1, 1]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k14t8p97, Certificates.k14t8p97_check⟩

private theorem k14t8_cover261 : ∀ P ∈ pathPatterns 0 0 [1, 1, 2], HasCheckedCertificate 14 8 ([[], [1, 1], [1, 1, 2]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k14t8p98, Certificates.k14t8p98_check⟩

private theorem k14t8_cover262 : ∀ P ∈ pathPatterns 1 1 [1, 2], HasCheckedCertificate 14 8 ([[], [1, 1], [1, 2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [1, 2] [] ∧ LexLE [] [])) h)

private theorem k14t8_cover263 : ∀ P ∈ pathPatterns 0 0 [1, 2, 1], HasCheckedCertificate 14 8 ([[], [1, 1], [1, 2, 1]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k14t8p99, Certificates.k14t8p99_check⟩

private theorem k14t8_cover264 : ∀ P ∈ pathPatterns 1 0 [1, 3], HasCheckedCertificate 14 8 ([[], [1, 1], [1, 3]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [1, 3] [] ∧ LexLE [] [])) h)

private theorem k14t8_cover266 : ∀ P ∈ pathPatterns 0 0 [2], HasCheckedCertificate 14 8 ([[], [1, 1], [2], [2]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k14t8p100, Certificates.k14t8p100_check⟩

private theorem k14t8_cover265 : ∀ P ∈ pathPatterns 2 2 [2], HasCheckedCertificate 14 8 ([[], [1, 1], [2]] ++ P) := by
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
            exact k14t8_cover266

private theorem k14t8_cover267 : ∀ P ∈ pathPatterns 1 0 [2, 2], HasCheckedCertificate 14 8 ([[], [1, 1], [2, 2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [2, 2] [] ∧ LexLE [] [])) h)

private theorem k14t8_cover268 : ∀ P ∈ pathPatterns 2 1 [3], HasCheckedCertificate 14 8 ([[], [1, 1], [3]] ++ P) := by
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

private theorem k14t8_cover269 : ∀ P ∈ pathPatterns 2 0 [4], HasCheckedCertificate 14 8 ([[], [1, 1], [4]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [4] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k14t8_cover258 : ∀ P ∈ pathPatterns 4 4 [1, 1], HasCheckedCertificate 14 8 ([[], [1, 1]] ++ P) := by
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
                  constructor
                  · exact by
                      intro _
                      exact k14t8_cover259
                  · intro q
                    fin_cases q
                    · exact by
                        intro _
                        exact k14t8_cover260
                    · exact by
                        intro _
                        exact k14t8_cover261
              · exact by
                  constructor
                  · exact by
                      intro _
                      exact k14t8_cover262
                  · intro q
                    fin_cases q
                    · exact by
                        intro _
                        exact k14t8_cover263
              · exact by
                  constructor
                  · exact by
                      intro _
                      exact k14t8_cover264
                  · intro q
                    exact Fin.elim0 q
        · exact by
            constructor
            · exact by
                intro _
                exact k14t8_cover265
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
                  constructor
                  · exact by
                      intro _
                      exact k14t8_cover267
                  · intro q
                    exact Fin.elim0 q
        · exact by
            constructor
            · exact by
                intro _
                exact k14t8_cover268
            · intro q
              fin_cases q
              · exact by
                  constructor
                  · exact by
                      intro h
                      exact False.elim ((by decide : ¬ (LexLE [1, 1] [3, 1] ∧ LexLE [3, 1] [1, 3])) h)
                  · intro q
                    exact Fin.elim0 q
        · exact by
            constructor
            · exact by
                intro _
                exact k14t8_cover269
            · intro q
              exact Fin.elim0 q

private theorem k14t8_cover271 : ∀ P ∈ pathPatterns 0 0 [1, 2], HasCheckedCertificate 14 8 ([[], [1, 1, 1], [1, 2]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k14t8p101, Certificates.k14t8p101_check⟩

private theorem k14t8_cover272 : ∀ P ∈ pathPatterns 1 1 [2], HasCheckedCertificate 14 8 ([[], [1, 1, 1], [2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [2] [] ∧ LexLE [] [])) h)

private theorem k14t8_cover273 : ∀ P ∈ pathPatterns 1 0 [3], HasCheckedCertificate 14 8 ([[], [1, 1, 1], [3]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [3] [] ∧ LexLE [] [])) h)

private theorem k14t8_cover270 : ∀ P ∈ pathPatterns 3 3 [1, 1, 1], HasCheckedCertificate 14 8 ([[], [1, 1, 1]] ++ P) := by
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
                  exact k14t8_cover271
        · exact by
            constructor
            · exact by
                intro _
                exact k14t8_cover272
            · intro q
              fin_cases q
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [1, 1, 1] [2, 1] ∧ LexLE [2, 1] [1, 2])) h)
        · exact by
            constructor
            · exact by
                intro _
                exact k14t8_cover273
            · intro q
              exact Fin.elim0 q

private theorem k14t8_cover275 : ∀ P ∈ pathPatterns 0 0 [2], HasCheckedCertificate 14 8 ([[], [1, 1, 1, 1], [2]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k14t8p102, Certificates.k14t8p102_check⟩

private theorem k14t8_cover274 : ∀ P ∈ pathPatterns 2 2 [1, 1, 1, 1], HasCheckedCertificate 14 8 ([[], [1, 1, 1, 1]] ++ P) := by
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
            exact k14t8_cover275

private theorem k14t8_cover276 : ∀ P ∈ pathPatterns 1 1 [1, 1, 1, 1, 1], HasCheckedCertificate 14 8 ([[], [1, 1, 1, 1, 1]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [1, 1, 1, 1, 1] [] ∧ LexLE [] [])) h)

private theorem k14t8_cover277 : ∀ P ∈ pathPatterns 0 0 [1, 1, 1, 1, 1, 1], HasCheckedCertificate 14 8 ([[], [1, 1, 1, 1, 1, 1]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k14t8p103, Certificates.k14t8p103_check⟩

private theorem k14t8_cover278 : ∀ P ∈ pathPatterns 1 0 [1, 1, 1, 1, 2], HasCheckedCertificate 14 8 ([[], [1, 1, 1, 1, 2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [1, 1, 1, 1, 2] [] ∧ LexLE [] [])) h)

private theorem k14t8_cover279 : ∀ P ∈ pathPatterns 2 1 [1, 1, 1, 2], HasCheckedCertificate 14 8 ([[], [1, 1, 1, 2]] ++ P) := by
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

private theorem k14t8_cover280 : ∀ P ∈ pathPatterns 1 0 [1, 1, 1, 2, 1], HasCheckedCertificate 14 8 ([[], [1, 1, 1, 2, 1]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [1, 1, 1, 2, 1] [] ∧ LexLE [] [])) h)

private theorem k14t8_cover281 : ∀ P ∈ pathPatterns 2 0 [1, 1, 1, 3], HasCheckedCertificate 14 8 ([[], [1, 1, 1, 3]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [1, 1, 1, 3] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k14t8_cover283 : ∀ P ∈ pathPatterns 1 0 [2], HasCheckedCertificate 14 8 ([[], [1, 1, 2], [2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [2] [] ∧ LexLE [] [])) h)

private theorem k14t8_cover282 : ∀ P ∈ pathPatterns 3 2 [1, 1, 2], HasCheckedCertificate 14 8 ([[], [1, 1, 2]] ++ P) := by
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
            constructor
            · exact by
                intro _
                exact k14t8_cover283
            · intro q
              exact Fin.elim0 q

private theorem k14t8_cover284 : ∀ P ∈ pathPatterns 2 1 [1, 1, 2, 1], HasCheckedCertificate 14 8 ([[], [1, 1, 2, 1]] ++ P) := by
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

private theorem k14t8_cover285 : ∀ P ∈ pathPatterns 1 0 [1, 1, 2, 1, 1], HasCheckedCertificate 14 8 ([[], [1, 1, 2, 1, 1]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [1, 1, 2, 1, 1] [] ∧ LexLE [] [])) h)

private theorem k14t8_cover286 : ∀ P ∈ pathPatterns 2 0 [1, 1, 2, 2], HasCheckedCertificate 14 8 ([[], [1, 1, 2, 2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [1, 1, 2, 2] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k14t8_cover287 : ∀ P ∈ pathPatterns 3 1 [1, 1, 3], HasCheckedCertificate 14 8 ([[], [1, 1, 3]] ++ P) := by
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
              exact Fin.elim0 q

private theorem k14t8_cover288 : ∀ P ∈ pathPatterns 2 0 [1, 1, 3, 1], HasCheckedCertificate 14 8 ([[], [1, 1, 3, 1]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [1, 1, 3, 1] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k14t8_cover289 : ∀ P ∈ pathPatterns 3 0 [1, 1, 4], HasCheckedCertificate 14 8 ([[], [1, 1, 4]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [1, 1, 4] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k14t8_cover291 : ∀ P ∈ pathPatterns 1 0 [1, 2], HasCheckedCertificate 14 8 ([[], [1, 2], [1, 2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [1, 2] [] ∧ LexLE [] [])) h)

private theorem k14t8_cover292 : ∀ P ∈ pathPatterns 2 1 [2], HasCheckedCertificate 14 8 ([[], [1, 2], [2]] ++ P) := by
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

private theorem k14t8_cover293 : ∀ P ∈ pathPatterns 2 0 [3], HasCheckedCertificate 14 8 ([[], [1, 2], [3]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [3] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k14t8_cover290 : ∀ P ∈ pathPatterns 4 3 [1, 2], HasCheckedCertificate 14 8 ([[], [1, 2]] ++ P) := by
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
                  constructor
                  · exact by
                      intro _
                      exact k14t8_cover291
                  · intro q
                    exact Fin.elim0 q
        · exact by
            constructor
            · exact by
                intro _
                exact k14t8_cover292
            · intro q
              fin_cases q
              · exact by
                  constructor
                  · exact by
                      intro h
                      exact False.elim ((by decide : ¬ (LexLE [1, 2] [2, 1] ∧ LexLE [2, 1] [1, 2])) h)
                  · intro q
                    exact Fin.elim0 q
        · exact by
            constructor
            · exact by
                intro _
                exact k14t8_cover293
            · intro q
              exact Fin.elim0 q

private theorem k14t8_cover295 : ∀ P ∈ pathPatterns 1 0 [2], HasCheckedCertificate 14 8 ([[], [1, 2, 1], [2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [2] [] ∧ LexLE [] [])) h)

private theorem k14t8_cover294 : ∀ P ∈ pathPatterns 3 2 [1, 2, 1], HasCheckedCertificate 14 8 ([[], [1, 2, 1]] ++ P) := by
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
            constructor
            · exact by
                intro _
                exact k14t8_cover295
            · intro q
              exact Fin.elim0 q

private theorem k14t8_cover296 : ∀ P ∈ pathPatterns 2 0 [1, 2, 1, 2], HasCheckedCertificate 14 8 ([[], [1, 2, 1, 2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [1, 2, 1, 2] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k14t8_cover297 : ∀ P ∈ pathPatterns 3 1 [1, 2, 2], HasCheckedCertificate 14 8 ([[], [1, 2, 2]] ++ P) := by
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
              exact Fin.elim0 q

private theorem k14t8_cover298 : ∀ P ∈ pathPatterns 2 0 [1, 2, 2, 1], HasCheckedCertificate 14 8 ([[], [1, 2, 2, 1]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [1, 2, 2, 1] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k14t8_cover299 : ∀ P ∈ pathPatterns 3 0 [1, 2, 3], HasCheckedCertificate 14 8 ([[], [1, 2, 3]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [1, 2, 3] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k14t8_cover301 : ∀ P ∈ pathPatterns 2 0 [2], HasCheckedCertificate 14 8 ([[], [1, 3], [2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [2] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k14t8_cover300 : ∀ P ∈ pathPatterns 4 2 [1, 3], HasCheckedCertificate 14 8 ([[], [1, 3]] ++ P) := by
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
                    exact Fin.elim0 q
        · exact by
            constructor
            · exact by
                intro _
                exact k14t8_cover301
            · intro q
              exact Fin.elim0 q

private theorem k14t8_cover302 : ∀ P ∈ pathPatterns 3 1 [1, 3, 1], HasCheckedCertificate 14 8 ([[], [1, 3, 1]] ++ P) := by
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
              exact Fin.elim0 q

private theorem k14t8_cover303 : ∀ P ∈ pathPatterns 3 0 [1, 3, 2], HasCheckedCertificate 14 8 ([[], [1, 3, 2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [1, 3, 2] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k14t8_cover304 : ∀ P ∈ pathPatterns 4 1 [1, 4], HasCheckedCertificate 14 8 ([[], [1, 4]] ++ P) := by
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
              exact Fin.elim0 q

private theorem k14t8_cover305 : ∀ P ∈ pathPatterns 3 0 [1, 4, 1], HasCheckedCertificate 14 8 ([[], [1, 4, 1]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [1, 4, 1] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k14t8_cover306 : ∀ P ∈ pathPatterns 4 0 [1, 5], HasCheckedCertificate 14 8 ([[], [1, 5]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [1, 5] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k14t8_seq221 : amountSequenceForall 5 5 (fun tail =>
    (LexLE [] ([1] ++ tail) ∧ LexLE ([1] ++ tail) ([1] ++ tail).reverse) →
    ∀ P ∈ pathPatterns (6 - ([1] ++ tail).length) (6 - ([1] ++ tail).sum) ([1] ++ tail),
      HasCheckedCertificate 14 8 ([[]] ++ (([1] ++ tail) :: P))) :=
by
  constructor
  · exact by
      intro _
      exact k14t8_cover222
  · intro q
    fin_cases q
    · exact by
        constructor
        · exact by
            intro _
            exact k14t8_cover258
        · intro q
          fin_cases q
          · exact by
              constructor
              · exact by
                  intro _
                  exact k14t8_cover270
              · intro q
                fin_cases q
                · exact by
                    constructor
                    · exact by
                        intro _
                        exact k14t8_cover274
                    · intro q
                      fin_cases q
                      · exact by
                          constructor
                          · exact by
                              intro _
                              exact k14t8_cover276
                          · intro q
                            fin_cases q
                            · exact by
                                intro _
                                exact k14t8_cover277
                      · exact by
                          constructor
                          · exact by
                              intro _
                              exact k14t8_cover278
                          · intro q
                            exact Fin.elim0 q
                · exact by
                    constructor
                    · exact by
                        intro _
                        exact k14t8_cover279
                    · intro q
                      fin_cases q
                      · exact by
                          constructor
                          · exact by
                              intro _
                              exact k14t8_cover280
                          · intro q
                            exact Fin.elim0 q
                · exact by
                    constructor
                    · exact by
                        intro _
                        exact k14t8_cover281
                    · intro q
                      exact Fin.elim0 q
          · exact by
              constructor
              · exact by
                  intro _
                  exact k14t8_cover282
              · intro q
                fin_cases q
                · exact by
                    constructor
                    · exact by
                        intro _
                        exact k14t8_cover284
                    · intro q
                      fin_cases q
                      · exact by
                          constructor
                          · exact by
                              intro _
                              exact k14t8_cover285
                          · intro q
                            exact Fin.elim0 q
                · exact by
                    constructor
                    · exact by
                        intro _
                        exact k14t8_cover286
                    · intro q
                      exact Fin.elim0 q
          · exact by
              constructor
              · exact by
                  intro _
                  exact k14t8_cover287
              · intro q
                fin_cases q
                · exact by
                    constructor
                    · exact by
                        intro _
                        exact k14t8_cover288
                    · intro q
                      exact Fin.elim0 q
          · exact by
              constructor
              · exact by
                  intro _
                  exact k14t8_cover289
              · intro q
                exact Fin.elim0 q
    · exact by
        constructor
        · exact by
            intro _
            exact k14t8_cover290
        · intro q
          fin_cases q
          · exact by
              constructor
              · exact by
                  intro _
                  exact k14t8_cover294
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
                            exact Fin.elim0 q
                · exact by
                    constructor
                    · exact by
                        intro _
                        exact k14t8_cover296
                    · intro q
                      exact Fin.elim0 q
          · exact by
              constructor
              · exact by
                  intro _
                  exact k14t8_cover297
              · intro q
                fin_cases q
                · exact by
                    constructor
                    · exact by
                        intro _
                        exact k14t8_cover298
                    · intro q
                      exact Fin.elim0 q
          · exact by
              constructor
              · exact by
                  intro _
                  exact k14t8_cover299
              · intro q
                exact Fin.elim0 q
    · exact by
        constructor
        · exact by
            intro _
            exact k14t8_cover300
        · intro q
          fin_cases q
          · exact by
              constructor
              · exact by
                  intro _
                  exact k14t8_cover302
              · intro q
                fin_cases q
                · exact by
                    constructor
                    · exact by
                        intro h
                        exact False.elim ((by decide : ¬ (LexLE [] [1, 3, 1, 1] ∧ LexLE [1, 3, 1, 1] [1, 1, 3, 1])) h)
                    · intro q
                      exact Fin.elim0 q
          · exact by
              constructor
              · exact by
                  intro _
                  exact k14t8_cover303
              · intro q
                exact Fin.elim0 q
    · exact by
        constructor
        · exact by
            intro _
            exact k14t8_cover304
        · intro q
          fin_cases q
          · exact by
              constructor
              · exact by
                  intro _
                  exact k14t8_cover305
              · intro q
                exact Fin.elim0 q
    · exact by
        constructor
        · exact by
            intro _
            exact k14t8_cover306
        · intro q
          exact Fin.elim0 q

private theorem k14t8_cover309 : ∀ P ∈ pathPatterns 1 0 [2], HasCheckedCertificate 14 8 ([[], [2], [2], [2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [2] [] ∧ LexLE [] [])) h)

private theorem k14t8_cover308 : ∀ P ∈ pathPatterns 3 2 [2], HasCheckedCertificate 14 8 ([[], [2], [2]] ++ P) := by
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
                exact k14t8_cover309
            · intro q
              exact Fin.elim0 q

private theorem k14t8_cover310 : ∀ P ∈ pathPatterns 2 0 [2, 2], HasCheckedCertificate 14 8 ([[], [2], [2, 2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [2, 2] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k14t8_cover311 : ∀ P ∈ pathPatterns 3 1 [3], HasCheckedCertificate 14 8 ([[], [2], [3]] ++ P) := by
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

private theorem k14t8_cover312 : ∀ P ∈ pathPatterns 3 0 [4], HasCheckedCertificate 14 8 ([[], [2], [4]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [4] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k14t8_cover307 : ∀ P ∈ pathPatterns 5 4 [2], HasCheckedCertificate 14 8 ([[], [2]] ++ P) := by
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
                        constructor
                        · exact by
                            intro h
                            exact False.elim ((by decide : ¬ (LexLE [2] [1, 1, 2] ∧ LexLE [1, 1, 2] [2, 1, 1])) h)
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
                          exact Fin.elim0 q
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
                exact k14t8_cover308
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
                          exact Fin.elim0 q
              · exact by
                  constructor
                  · exact by
                      intro _
                      exact k14t8_cover310
                  · intro q
                    exact Fin.elim0 q
        · exact by
            constructor
            · exact by
                intro _
                exact k14t8_cover311
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
                exact k14t8_cover312
            · intro q
              exact Fin.elim0 q

private theorem k14t8_cover313 : ∀ P ∈ pathPatterns 2 0 [2, 1, 1, 2], HasCheckedCertificate 14 8 ([[], [2, 1, 1, 2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [2, 1, 1, 2] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k14t8_cover314 : ∀ P ∈ pathPatterns 3 1 [2, 1, 2], HasCheckedCertificate 14 8 ([[], [2, 1, 2]] ++ P) := by
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
              exact Fin.elim0 q

private theorem k14t8_cover315 : ∀ P ∈ pathPatterns 3 0 [2, 1, 3], HasCheckedCertificate 14 8 ([[], [2, 1, 3]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [2, 1, 3] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k14t8_cover316 : ∀ P ∈ pathPatterns 4 2 [2, 2], HasCheckedCertificate 14 8 ([[], [2, 2]] ++ P) := by
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
                    exact Fin.elim0 q
        · exact by
            constructor
            · exact by
                intro h
                exact False.elim ((by decide : ¬ (LexLE [2, 2] [2] ∧ LexLE [2] [2])) h)
            · intro q
              exact Fin.elim0 q

private theorem k14t8_cover317 : ∀ P ∈ pathPatterns 3 0 [2, 2, 2], HasCheckedCertificate 14 8 ([[], [2, 2, 2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [2, 2, 2] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k14t8_cover318 : ∀ P ∈ pathPatterns 4 1 [2, 3], HasCheckedCertificate 14 8 ([[], [2, 3]] ++ P) := by
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

private theorem k14t8_cover319 : ∀ P ∈ pathPatterns 4 0 [2, 4], HasCheckedCertificate 14 8 ([[], [2, 4]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [2, 4] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k14t8_cover321 : ∀ P ∈ pathPatterns 3 0 [3], HasCheckedCertificate 14 8 ([[], [3], [3]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [3] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k14t8_cover320 : ∀ P ∈ pathPatterns 5 3 [3], HasCheckedCertificate 14 8 ([[], [3]] ++ P) := by
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
                        constructor
                        · exact by
                            intro h
                            exact False.elim ((by decide : ¬ (LexLE [3] [1, 1, 1] ∧ LexLE [1, 1, 1] [1, 1, 1])) h)
                        · intro q
                          exact Fin.elim0 q
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
                exact k14t8_cover321
            · intro q
              exact Fin.elim0 q

private theorem k14t8_cover322 : ∀ P ∈ pathPatterns 4 0 [3, 3], HasCheckedCertificate 14 8 ([[], [3, 3]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [3, 3] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k14t8_cover323 : ∀ P ∈ pathPatterns 5 2 [4], HasCheckedCertificate 14 8 ([[], [4]] ++ P) := by
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

private theorem k14t8_cover324 : ∀ P ∈ pathPatterns 5 1 [5], HasCheckedCertificate 14 8 ([[], [5]] ++ P) := by
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

private theorem k14t8_cover325 : ∀ P ∈ pathPatterns 5 0 [6], HasCheckedCertificate 14 8 ([[], [6]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [6] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k14t8_seq4 : amountSequenceForall 6 6 (fun tail =>
    (LexLE [] ([] ++ tail) ∧ LexLE ([] ++ tail) ([] ++ tail).reverse) →
    ∀ P ∈ pathPatterns (6 - ([] ++ tail).length) (6 - ([] ++ tail).sum) ([] ++ tail),
      HasCheckedCertificate 14 8 ([[]] ++ (([] ++ tail) :: P))) :=
by
  constructor
  · exact by
      intro _
      exact k14t8_cover5
  · intro q
    fin_cases q
    · exact k14t8_seq221

    · exact by
        constructor
        · exact by
            intro _
            exact k14t8_cover307
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
                                  exact Fin.elim0 q
                      · exact by
                          constructor
                          · exact by
                              intro _
                              exact k14t8_cover313
                          · intro q
                            exact Fin.elim0 q
                · exact by
                    constructor
                    · exact by
                        intro _
                        exact k14t8_cover314
                    · intro q
                      fin_cases q
                      · exact by
                          constructor
                          · exact by
                              intro h
                              exact False.elim ((by decide : ¬ (LexLE [] [2, 1, 2, 1] ∧ LexLE [2, 1, 2, 1] [1, 2, 1, 2])) h)
                          · intro q
                            exact Fin.elim0 q
                · exact by
                    constructor
                    · exact by
                        intro _
                        exact k14t8_cover315
                    · intro q
                      exact Fin.elim0 q
          · exact by
              constructor
              · exact by
                  intro _
                  exact k14t8_cover316
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
                            exact Fin.elim0 q
                · exact by
                    constructor
                    · exact by
                        intro _
                        exact k14t8_cover317
                    · intro q
                      exact Fin.elim0 q
          · exact by
              constructor
              · exact by
                  intro _
                  exact k14t8_cover318
              · intro q
                fin_cases q
                · exact by
                    constructor
                    · exact by
                        intro h
                        exact False.elim ((by decide : ¬ (LexLE [] [2, 3, 1] ∧ LexLE [2, 3, 1] [1, 3, 2])) h)
                    · intro q
                      exact Fin.elim0 q
          · exact by
              constructor
              · exact by
                  intro _
                  exact k14t8_cover319
              · intro q
                exact Fin.elim0 q
    · exact by
        constructor
        · exact by
            intro _
            exact k14t8_cover320
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
                            exact Fin.elim0 q
                · exact by
                    constructor
                    · exact by
                        intro h
                        exact False.elim ((by decide : ¬ (LexLE [] [3, 1, 2] ∧ LexLE [3, 1, 2] [2, 1, 3])) h)
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
                      exact Fin.elim0 q
          · exact by
              constructor
              · exact by
                  intro _
                  exact k14t8_cover322
              · intro q
                exact Fin.elim0 q
    · exact by
        constructor
        · exact by
            intro _
            exact k14t8_cover323
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
                      exact Fin.elim0 q
          · exact by
              constructor
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [] [4, 2] ∧ LexLE [4, 2] [2, 4])) h)
              · intro q
                exact Fin.elim0 q
    · exact by
        constructor
        · exact by
            intro _
            exact k14t8_cover324
        · intro q
          fin_cases q
          · exact by
              constructor
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [] [5, 1] ∧ LexLE [5, 1] [1, 5])) h)
              · intro q
                exact Fin.elim0 q
    · exact by
        constructor
        · exact by
            intro _
            exact k14t8_cover325
        · intro q
          exact Fin.elim0 q

private theorem k14t8_cover3 : ∀ P ∈ pathPatterns 7 6 [], HasCheckedCertificate 14 8 ([[]] ++ P) := by
  apply pathPatterns_forall_step
  exact k14t8_seq4


private theorem k14t8_cover331 : ∀ P ∈ pathPatterns 0 2 [1], HasCheckedCertificate 14 8 ([[1], [1], [1], [1]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k14t8p104, Certificates.k14t8p104_check⟩

private theorem k14t8_cover332 : ∀ P ∈ pathPatterns 0 1 [2], HasCheckedCertificate 14 8 ([[1], [1], [1], [2]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k14t8p105, Certificates.k14t8p105_check⟩

private theorem k14t8_cover333 : ∀ P ∈ pathPatterns 0 0 [3], HasCheckedCertificate 14 8 ([[1], [1], [1], [3]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k14t8p106, Certificates.k14t8p106_check⟩

private theorem k14t8_cover330 : ∀ P ∈ pathPatterns 2 3 [1], HasCheckedCertificate 14 8 ([[1], [1], [1]] ++ P) := by
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
            exact k14t8_cover331
        · exact by
            intro _
            exact k14t8_cover332
        · exact by
            intro _
            exact k14t8_cover333

private theorem k14t8_cover334 : ∀ P ∈ pathPatterns 1 2 [1, 1], HasCheckedCertificate 14 8 ([[1], [1], [1, 1]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [1, 1] [] ∧ LexLE [] [])) h)

private theorem k14t8_cover335 : ∀ P ∈ pathPatterns 0 1 [1, 1, 1], HasCheckedCertificate 14 8 ([[1], [1], [1, 1, 1]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k14t8p107, Certificates.k14t8p107_check⟩

private theorem k14t8_cover336 : ∀ P ∈ pathPatterns 0 0 [1, 1, 2], HasCheckedCertificate 14 8 ([[1], [1], [1, 1, 2]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k14t8p108, Certificates.k14t8p108_check⟩

private theorem k14t8_cover337 : ∀ P ∈ pathPatterns 1 1 [1, 2], HasCheckedCertificate 14 8 ([[1], [1], [1, 2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [1, 2] [] ∧ LexLE [] [])) h)

private theorem k14t8_cover338 : ∀ P ∈ pathPatterns 0 0 [1, 2, 1], HasCheckedCertificate 14 8 ([[1], [1], [1, 2, 1]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k14t8p109, Certificates.k14t8p109_check⟩

private theorem k14t8_cover339 : ∀ P ∈ pathPatterns 1 0 [1, 3], HasCheckedCertificate 14 8 ([[1], [1], [1, 3]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [1, 3] [] ∧ LexLE [] [])) h)

private theorem k14t8_cover341 : ∀ P ∈ pathPatterns 0 0 [2], HasCheckedCertificate 14 8 ([[1], [1], [2], [2]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k14t8p110, Certificates.k14t8p110_check⟩

private theorem k14t8_cover340 : ∀ P ∈ pathPatterns 2 2 [2], HasCheckedCertificate 14 8 ([[1], [1], [2]] ++ P) := by
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
            exact k14t8_cover341

private theorem k14t8_cover342 : ∀ P ∈ pathPatterns 1 0 [2, 2], HasCheckedCertificate 14 8 ([[1], [1], [2, 2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [2, 2] [] ∧ LexLE [] [])) h)

private theorem k14t8_cover343 : ∀ P ∈ pathPatterns 2 1 [3], HasCheckedCertificate 14 8 ([[1], [1], [3]] ++ P) := by
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

private theorem k14t8_cover344 : ∀ P ∈ pathPatterns 2 0 [4], HasCheckedCertificate 14 8 ([[1], [1], [4]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [4] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k14t8_cover329 : ∀ P ∈ pathPatterns 4 4 [1], HasCheckedCertificate 14 8 ([[1], [1]] ++ P) := by
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
                exact k14t8_cover330
            · intro q
              fin_cases q
              · exact by
                  constructor
                  · exact by
                      intro _
                      exact k14t8_cover334
                  · intro q
                    fin_cases q
                    · exact by
                        intro _
                        exact k14t8_cover335
                    · exact by
                        intro _
                        exact k14t8_cover336
              · exact by
                  constructor
                  · exact by
                      intro _
                      exact k14t8_cover337
                  · intro q
                    fin_cases q
                    · exact by
                        intro _
                        exact k14t8_cover338
              · exact by
                  constructor
                  · exact by
                      intro _
                      exact k14t8_cover339
                  · intro q
                    exact Fin.elim0 q
        · exact by
            constructor
            · exact by
                intro _
                exact k14t8_cover340
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
                  constructor
                  · exact by
                      intro _
                      exact k14t8_cover342
                  · intro q
                    exact Fin.elim0 q
        · exact by
            constructor
            · exact by
                intro _
                exact k14t8_cover343
            · intro q
              fin_cases q
              · exact by
                  constructor
                  · exact by
                      intro h
                      exact False.elim ((by decide : ¬ (LexLE [1] [3, 1] ∧ LexLE [3, 1] [1, 3])) h)
                  · intro q
                    exact Fin.elim0 q
        · exact by
            constructor
            · exact by
                intro _
                exact k14t8_cover344
            · intro q
              exact Fin.elim0 q

private theorem k14t8_cover346 : ∀ P ∈ pathPatterns 0 1 [1, 1], HasCheckedCertificate 14 8 ([[1], [1, 1], [1, 1]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k14t8p111, Certificates.k14t8p111_check⟩

private theorem k14t8_cover347 : ∀ P ∈ pathPatterns 0 0 [1, 2], HasCheckedCertificate 14 8 ([[1], [1, 1], [1, 2]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k14t8p112, Certificates.k14t8p112_check⟩

private theorem k14t8_cover348 : ∀ P ∈ pathPatterns 1 1 [2], HasCheckedCertificate 14 8 ([[1], [1, 1], [2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [2] [] ∧ LexLE [] [])) h)

private theorem k14t8_cover349 : ∀ P ∈ pathPatterns 1 0 [3], HasCheckedCertificate 14 8 ([[1], [1, 1], [3]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [3] [] ∧ LexLE [] [])) h)

private theorem k14t8_cover345 : ∀ P ∈ pathPatterns 3 3 [1, 1], HasCheckedCertificate 14 8 ([[1], [1, 1]] ++ P) := by
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
                  exact k14t8_cover346
              · exact by
                  intro _
                  exact k14t8_cover347
        · exact by
            constructor
            · exact by
                intro _
                exact k14t8_cover348
            · intro q
              fin_cases q
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [1, 1] [2, 1] ∧ LexLE [2, 1] [1, 2])) h)
        · exact by
            constructor
            · exact by
                intro _
                exact k14t8_cover349
            · intro q
              exact Fin.elim0 q

private theorem k14t8_cover351 : ∀ P ∈ pathPatterns 0 0 [2], HasCheckedCertificate 14 8 ([[1], [1, 1, 1], [2]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k14t8p113, Certificates.k14t8p113_check⟩

private theorem k14t8_cover350 : ∀ P ∈ pathPatterns 2 2 [1, 1, 1], HasCheckedCertificate 14 8 ([[1], [1, 1, 1]] ++ P) := by
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
            exact k14t8_cover351

private theorem k14t8_cover352 : ∀ P ∈ pathPatterns 1 1 [1, 1, 1, 1], HasCheckedCertificate 14 8 ([[1], [1, 1, 1, 1]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [1, 1, 1, 1] [] ∧ LexLE [] [])) h)

private theorem k14t8_cover353 : ∀ P ∈ pathPatterns 0 0 [1, 1, 1, 1, 1], HasCheckedCertificate 14 8 ([[1], [1, 1, 1, 1, 1]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k14t8p114, Certificates.k14t8p114_check⟩

private theorem k14t8_cover354 : ∀ P ∈ pathPatterns 1 0 [1, 1, 1, 2], HasCheckedCertificate 14 8 ([[1], [1, 1, 1, 2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [1, 1, 1, 2] [] ∧ LexLE [] [])) h)

private theorem k14t8_cover355 : ∀ P ∈ pathPatterns 2 1 [1, 1, 2], HasCheckedCertificate 14 8 ([[1], [1, 1, 2]] ++ P) := by
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

private theorem k14t8_cover356 : ∀ P ∈ pathPatterns 1 0 [1, 1, 2, 1], HasCheckedCertificate 14 8 ([[1], [1, 1, 2, 1]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [1, 1, 2, 1] [] ∧ LexLE [] [])) h)

private theorem k14t8_cover357 : ∀ P ∈ pathPatterns 2 0 [1, 1, 3], HasCheckedCertificate 14 8 ([[1], [1, 1, 3]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [1, 1, 3] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k14t8_cover359 : ∀ P ∈ pathPatterns 1 0 [2], HasCheckedCertificate 14 8 ([[1], [1, 2], [2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [2] [] ∧ LexLE [] [])) h)

private theorem k14t8_cover358 : ∀ P ∈ pathPatterns 3 2 [1, 2], HasCheckedCertificate 14 8 ([[1], [1, 2]] ++ P) := by
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
            constructor
            · exact by
                intro _
                exact k14t8_cover359
            · intro q
              exact Fin.elim0 q

private theorem k14t8_cover360 : ∀ P ∈ pathPatterns 2 1 [1, 2, 1], HasCheckedCertificate 14 8 ([[1], [1, 2, 1]] ++ P) := by
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

private theorem k14t8_cover361 : ∀ P ∈ pathPatterns 2 0 [1, 2, 2], HasCheckedCertificate 14 8 ([[1], [1, 2, 2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [1, 2, 2] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k14t8_cover362 : ∀ P ∈ pathPatterns 3 1 [1, 3], HasCheckedCertificate 14 8 ([[1], [1, 3]] ++ P) := by
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
              exact Fin.elim0 q

private theorem k14t8_cover363 : ∀ P ∈ pathPatterns 2 0 [1, 3, 1], HasCheckedCertificate 14 8 ([[1], [1, 3, 1]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [1, 3, 1] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k14t8_cover364 : ∀ P ∈ pathPatterns 3 0 [1, 4], HasCheckedCertificate 14 8 ([[1], [1, 4]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [1, 4] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k14t8_cover366 : ∀ P ∈ pathPatterns 2 1 [2], HasCheckedCertificate 14 8 ([[1], [2], [2]] ++ P) := by
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

private theorem k14t8_cover367 : ∀ P ∈ pathPatterns 2 0 [3], HasCheckedCertificate 14 8 ([[1], [2], [3]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [3] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k14t8_cover365 : ∀ P ∈ pathPatterns 4 3 [2], HasCheckedCertificate 14 8 ([[1], [2]] ++ P) := by
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
                  constructor
                  · exact by
                      intro h
                      exact False.elim ((by decide : ¬ (LexLE [2] [1, 2] ∧ LexLE [1, 2] [2, 1])) h)
                  · intro q
                    exact Fin.elim0 q
        · exact by
            constructor
            · exact by
                intro _
                exact k14t8_cover366
            · intro q
              fin_cases q
              · exact by
                  constructor
                  · exact by
                      intro h
                      exact False.elim ((by decide : ¬ (LexLE [2] [2, 1] ∧ LexLE [2, 1] [1, 2])) h)
                  · intro q
                    exact Fin.elim0 q
        · exact by
            constructor
            · exact by
                intro _
                exact k14t8_cover367
            · intro q
              exact Fin.elim0 q

private theorem k14t8_cover368 : ∀ P ∈ pathPatterns 2 0 [2, 1, 2], HasCheckedCertificate 14 8 ([[1], [2, 1, 2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [2, 1, 2] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k14t8_cover369 : ∀ P ∈ pathPatterns 3 1 [2, 2], HasCheckedCertificate 14 8 ([[1], [2, 2]] ++ P) := by
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
              exact Fin.elim0 q

private theorem k14t8_cover370 : ∀ P ∈ pathPatterns 3 0 [2, 3], HasCheckedCertificate 14 8 ([[1], [2, 3]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [2, 3] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k14t8_cover371 : ∀ P ∈ pathPatterns 4 2 [3], HasCheckedCertificate 14 8 ([[1], [3]] ++ P) := by
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

private theorem k14t8_cover372 : ∀ P ∈ pathPatterns 4 1 [4], HasCheckedCertificate 14 8 ([[1], [4]] ++ P) := by
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

private theorem k14t8_cover373 : ∀ P ∈ pathPatterns 4 0 [5], HasCheckedCertificate 14 8 ([[1], [5]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [5] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k14t8_seq328 : amountSequenceForall 5 5 (fun tail =>
    (LexLE [1] ([] ++ tail) ∧ LexLE ([] ++ tail) ([] ++ tail).reverse) →
    ∀ P ∈ pathPatterns (5 - ([] ++ tail).length) (5 - ([] ++ tail).sum) ([] ++ tail),
      HasCheckedCertificate 14 8 ([[1]] ++ (([] ++ tail) :: P))) :=
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
            exact k14t8_cover329
        · intro q
          fin_cases q
          · exact by
              constructor
              · exact by
                  intro _
                  exact k14t8_cover345
              · intro q
                fin_cases q
                · exact by
                    constructor
                    · exact by
                        intro _
                        exact k14t8_cover350
                    · intro q
                      fin_cases q
                      · exact by
                          constructor
                          · exact by
                              intro _
                              exact k14t8_cover352
                          · intro q
                            fin_cases q
                            · exact by
                                intro _
                                exact k14t8_cover353
                      · exact by
                          constructor
                          · exact by
                              intro _
                              exact k14t8_cover354
                          · intro q
                            exact Fin.elim0 q
                · exact by
                    constructor
                    · exact by
                        intro _
                        exact k14t8_cover355
                    · intro q
                      fin_cases q
                      · exact by
                          constructor
                          · exact by
                              intro _
                              exact k14t8_cover356
                          · intro q
                            exact Fin.elim0 q
                · exact by
                    constructor
                    · exact by
                        intro _
                        exact k14t8_cover357
                    · intro q
                      exact Fin.elim0 q
          · exact by
              constructor
              · exact by
                  intro _
                  exact k14t8_cover358
              · intro q
                fin_cases q
                · exact by
                    constructor
                    · exact by
                        intro _
                        exact k14t8_cover360
                    · intro q
                      fin_cases q
                      · exact by
                          constructor
                          · exact by
                              intro h
                              exact False.elim ((by decide : ¬ (LexLE [1] [1, 2, 1, 1] ∧ LexLE [1, 2, 1, 1] [1, 1, 2, 1])) h)
                          · intro q
                            exact Fin.elim0 q
                · exact by
                    constructor
                    · exact by
                        intro _
                        exact k14t8_cover361
                    · intro q
                      exact Fin.elim0 q
          · exact by
              constructor
              · exact by
                  intro _
                  exact k14t8_cover362
              · intro q
                fin_cases q
                · exact by
                    constructor
                    · exact by
                        intro _
                        exact k14t8_cover363
                    · intro q
                      exact Fin.elim0 q
          · exact by
              constructor
              · exact by
                  intro _
                  exact k14t8_cover364
              · intro q
                exact Fin.elim0 q
    · exact by
        constructor
        · exact by
            intro _
            exact k14t8_cover365
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
                            exact Fin.elim0 q
                · exact by
                    constructor
                    · exact by
                        intro _
                        exact k14t8_cover368
                    · intro q
                      exact Fin.elim0 q
          · exact by
              constructor
              · exact by
                  intro _
                  exact k14t8_cover369
              · intro q
                fin_cases q
                · exact by
                    constructor
                    · exact by
                        intro h
                        exact False.elim ((by decide : ¬ (LexLE [1] [2, 2, 1] ∧ LexLE [2, 2, 1] [1, 2, 2])) h)
                    · intro q
                      exact Fin.elim0 q
          · exact by
              constructor
              · exact by
                  intro _
                  exact k14t8_cover370
              · intro q
                exact Fin.elim0 q
    · exact by
        constructor
        · exact by
            intro _
            exact k14t8_cover371
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
                      exact Fin.elim0 q
          · exact by
              constructor
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [1] [3, 2] ∧ LexLE [3, 2] [2, 3])) h)
              · intro q
                exact Fin.elim0 q
    · exact by
        constructor
        · exact by
            intro _
            exact k14t8_cover372
        · intro q
          fin_cases q
          · exact by
              constructor
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [1] [4, 1] ∧ LexLE [4, 1] [1, 4])) h)
              · intro q
                exact Fin.elim0 q
    · exact by
        constructor
        · exact by
            intro _
            exact k14t8_cover373
        · intro q
          exact Fin.elim0 q

private theorem k14t8_cover327 : ∀ P ∈ pathPatterns 6 5 [1], HasCheckedCertificate 14 8 ([[1]] ++ P) := by
  apply pathPatterns_forall_step
  exact k14t8_seq328


private theorem k14t8_cover376 : ∀ P ∈ pathPatterns 0 0 [2], HasCheckedCertificate 14 8 ([[1, 1], [1, 1], [2]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k14t8p115, Certificates.k14t8p115_check⟩

private theorem k14t8_cover375 : ∀ P ∈ pathPatterns 2 2 [1, 1], HasCheckedCertificate 14 8 ([[1, 1], [1, 1]] ++ P) := by
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
            exact k14t8_cover376

private theorem k14t8_cover377 : ∀ P ∈ pathPatterns 1 1 [1, 1, 1], HasCheckedCertificate 14 8 ([[1, 1], [1, 1, 1]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [1, 1, 1] [] ∧ LexLE [] [])) h)

private theorem k14t8_cover378 : ∀ P ∈ pathPatterns 0 0 [1, 1, 1, 1], HasCheckedCertificate 14 8 ([[1, 1], [1, 1, 1, 1]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k14t8p116, Certificates.k14t8p116_check⟩

private theorem k14t8_cover379 : ∀ P ∈ pathPatterns 1 0 [1, 1, 2], HasCheckedCertificate 14 8 ([[1, 1], [1, 1, 2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [1, 1, 2] [] ∧ LexLE [] [])) h)

private theorem k14t8_cover380 : ∀ P ∈ pathPatterns 2 1 [1, 2], HasCheckedCertificate 14 8 ([[1, 1], [1, 2]] ++ P) := by
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

private theorem k14t8_cover381 : ∀ P ∈ pathPatterns 1 0 [1, 2, 1], HasCheckedCertificate 14 8 ([[1, 1], [1, 2, 1]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [1, 2, 1] [] ∧ LexLE [] [])) h)

private theorem k14t8_cover382 : ∀ P ∈ pathPatterns 2 0 [1, 3], HasCheckedCertificate 14 8 ([[1, 1], [1, 3]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [1, 3] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k14t8_cover384 : ∀ P ∈ pathPatterns 1 0 [2], HasCheckedCertificate 14 8 ([[1, 1], [2], [2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [2] [] ∧ LexLE [] [])) h)

private theorem k14t8_cover383 : ∀ P ∈ pathPatterns 3 2 [2], HasCheckedCertificate 14 8 ([[1, 1], [2]] ++ P) := by
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
                exact k14t8_cover384
            · intro q
              exact Fin.elim0 q

private theorem k14t8_cover385 : ∀ P ∈ pathPatterns 2 0 [2, 2], HasCheckedCertificate 14 8 ([[1, 1], [2, 2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [2, 2] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k14t8_cover386 : ∀ P ∈ pathPatterns 3 1 [3], HasCheckedCertificate 14 8 ([[1, 1], [3]] ++ P) := by
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

private theorem k14t8_cover387 : ∀ P ∈ pathPatterns 3 0 [4], HasCheckedCertificate 14 8 ([[1, 1], [4]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [4] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k14t8_cover374 : ∀ P ∈ pathPatterns 5 4 [1, 1], HasCheckedCertificate 14 8 ([[1, 1]] ++ P) := by
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
                  constructor
                  · exact by
                      intro _
                      exact k14t8_cover375
                  · intro q
                    fin_cases q
                    · exact by
                        constructor
                        · exact by
                            intro _
                            exact k14t8_cover377
                        · intro q
                          fin_cases q
                          · exact by
                              intro _
                              exact k14t8_cover378
                    · exact by
                        constructor
                        · exact by
                            intro _
                            exact k14t8_cover379
                        · intro q
                          exact Fin.elim0 q
              · exact by
                  constructor
                  · exact by
                      intro _
                      exact k14t8_cover380
                  · intro q
                    fin_cases q
                    · exact by
                        constructor
                        · exact by
                            intro _
                            exact k14t8_cover381
                        · intro q
                          exact Fin.elim0 q
              · exact by
                  constructor
                  · exact by
                      intro _
                      exact k14t8_cover382
                  · intro q
                    exact Fin.elim0 q
        · exact by
            constructor
            · exact by
                intro _
                exact k14t8_cover383
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
                          exact Fin.elim0 q
              · exact by
                  constructor
                  · exact by
                      intro _
                      exact k14t8_cover385
                  · intro q
                    exact Fin.elim0 q
        · exact by
            constructor
            · exact by
                intro _
                exact k14t8_cover386
            · intro q
              fin_cases q
              · exact by
                  constructor
                  · exact by
                      intro h
                      exact False.elim ((by decide : ¬ (LexLE [1, 1] [3, 1] ∧ LexLE [3, 1] [1, 3])) h)
                  · intro q
                    exact Fin.elim0 q
        · exact by
            constructor
            · exact by
                intro _
                exact k14t8_cover387
            · intro q
              exact Fin.elim0 q

private theorem k14t8_cover389 : ∀ P ∈ pathPatterns 0 0 [1, 1, 1], HasCheckedCertificate 14 8 ([[1, 1, 1], [1, 1, 1]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k14t8p117, Certificates.k14t8p117_check⟩

private theorem k14t8_cover390 : ∀ P ∈ pathPatterns 1 0 [1, 2], HasCheckedCertificate 14 8 ([[1, 1, 1], [1, 2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [1, 2] [] ∧ LexLE [] [])) h)

private theorem k14t8_cover391 : ∀ P ∈ pathPatterns 2 1 [2], HasCheckedCertificate 14 8 ([[1, 1, 1], [2]] ++ P) := by
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

private theorem k14t8_cover392 : ∀ P ∈ pathPatterns 2 0 [3], HasCheckedCertificate 14 8 ([[1, 1, 1], [3]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [3] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k14t8_cover388 : ∀ P ∈ pathPatterns 4 3 [1, 1, 1], HasCheckedCertificate 14 8 ([[1, 1, 1]] ++ P) := by
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
                  constructor
                  · exact by
                      intro h
                      exact False.elim ((by decide : ¬ (LexLE [1, 1, 1] [1, 1] ∧ LexLE [1, 1] [1, 1])) h)
                  · intro q
                    fin_cases q
                    · exact by
                        intro _
                        exact k14t8_cover389
              · exact by
                  constructor
                  · exact by
                      intro _
                      exact k14t8_cover390
                  · intro q
                    exact Fin.elim0 q
        · exact by
            constructor
            · exact by
                intro _
                exact k14t8_cover391
            · intro q
              fin_cases q
              · exact by
                  constructor
                  · exact by
                      intro h
                      exact False.elim ((by decide : ¬ (LexLE [1, 1, 1] [2, 1] ∧ LexLE [2, 1] [1, 2])) h)
                  · intro q
                    exact Fin.elim0 q
        · exact by
            constructor
            · exact by
                intro _
                exact k14t8_cover392
            · intro q
              exact Fin.elim0 q

private theorem k14t8_cover394 : ∀ P ∈ pathPatterns 1 0 [2], HasCheckedCertificate 14 8 ([[1, 1, 1, 1], [2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [2] [] ∧ LexLE [] [])) h)

private theorem k14t8_cover393 : ∀ P ∈ pathPatterns 3 2 [1, 1, 1, 1], HasCheckedCertificate 14 8 ([[1, 1, 1, 1]] ++ P) := by
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
            constructor
            · exact by
                intro _
                exact k14t8_cover394
            · intro q
              exact Fin.elim0 q

private theorem k14t8_cover395 : ∀ P ∈ pathPatterns 2 1 [1, 1, 1, 1, 1], HasCheckedCertificate 14 8 ([[1, 1, 1, 1, 1]] ++ P) := by
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

private theorem k14t8_cover396 : ∀ P ∈ pathPatterns 1 0 [1, 1, 1, 1, 1, 1], HasCheckedCertificate 14 8 ([[1, 1, 1, 1, 1, 1]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [1, 1, 1, 1, 1, 1] [] ∧ LexLE [] [])) h)

private theorem k14t8_cover397 : ∀ P ∈ pathPatterns 2 0 [1, 1, 1, 1, 2], HasCheckedCertificate 14 8 ([[1, 1, 1, 1, 2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [1, 1, 1, 1, 2] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k14t8_cover398 : ∀ P ∈ pathPatterns 3 1 [1, 1, 1, 2], HasCheckedCertificate 14 8 ([[1, 1, 1, 2]] ++ P) := by
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
              exact Fin.elim0 q

private theorem k14t8_cover399 : ∀ P ∈ pathPatterns 2 0 [1, 1, 1, 2, 1], HasCheckedCertificate 14 8 ([[1, 1, 1, 2, 1]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [1, 1, 1, 2, 1] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k14t8_cover400 : ∀ P ∈ pathPatterns 3 0 [1, 1, 1, 3], HasCheckedCertificate 14 8 ([[1, 1, 1, 3]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [1, 1, 1, 3] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k14t8_cover402 : ∀ P ∈ pathPatterns 2 0 [2], HasCheckedCertificate 14 8 ([[1, 1, 2], [2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [2] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k14t8_cover401 : ∀ P ∈ pathPatterns 4 2 [1, 1, 2], HasCheckedCertificate 14 8 ([[1, 1, 2]] ++ P) := by
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
                    exact Fin.elim0 q
        · exact by
            constructor
            · exact by
                intro _
                exact k14t8_cover402
            · intro q
              exact Fin.elim0 q

private theorem k14t8_cover403 : ∀ P ∈ pathPatterns 3 1 [1, 1, 2, 1], HasCheckedCertificate 14 8 ([[1, 1, 2, 1]] ++ P) := by
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
              exact Fin.elim0 q

private theorem k14t8_cover404 : ∀ P ∈ pathPatterns 2 0 [1, 1, 2, 1, 1], HasCheckedCertificate 14 8 ([[1, 1, 2, 1, 1]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [1, 1, 2, 1, 1] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k14t8_cover405 : ∀ P ∈ pathPatterns 3 0 [1, 1, 2, 2], HasCheckedCertificate 14 8 ([[1, 1, 2, 2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [1, 1, 2, 2] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k14t8_cover406 : ∀ P ∈ pathPatterns 4 1 [1, 1, 3], HasCheckedCertificate 14 8 ([[1, 1, 3]] ++ P) := by
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
              exact Fin.elim0 q

private theorem k14t8_cover407 : ∀ P ∈ pathPatterns 3 0 [1, 1, 3, 1], HasCheckedCertificate 14 8 ([[1, 1, 3, 1]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [1, 1, 3, 1] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k14t8_cover408 : ∀ P ∈ pathPatterns 4 0 [1, 1, 4], HasCheckedCertificate 14 8 ([[1, 1, 4]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [1, 1, 4] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k14t8_cover410 : ∀ P ∈ pathPatterns 2 0 [1, 2], HasCheckedCertificate 14 8 ([[1, 2], [1, 2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [1, 2] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k14t8_cover411 : ∀ P ∈ pathPatterns 3 1 [2], HasCheckedCertificate 14 8 ([[1, 2], [2]] ++ P) := by
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

private theorem k14t8_cover412 : ∀ P ∈ pathPatterns 3 0 [3], HasCheckedCertificate 14 8 ([[1, 2], [3]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [3] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k14t8_cover409 : ∀ P ∈ pathPatterns 5 3 [1, 2], HasCheckedCertificate 14 8 ([[1, 2]] ++ P) := by
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
                          exact Fin.elim0 q
              · exact by
                  constructor
                  · exact by
                      intro _
                      exact k14t8_cover410
                  · intro q
                    exact Fin.elim0 q
        · exact by
            constructor
            · exact by
                intro _
                exact k14t8_cover411
            · intro q
              fin_cases q
              · exact by
                  constructor
                  · exact by
                      intro h
                      exact False.elim ((by decide : ¬ (LexLE [1, 2] [2, 1] ∧ LexLE [2, 1] [1, 2])) h)
                  · intro q
                    exact Fin.elim0 q
        · exact by
            constructor
            · exact by
                intro _
                exact k14t8_cover412
            · intro q
              exact Fin.elim0 q

private theorem k14t8_cover414 : ∀ P ∈ pathPatterns 2 0 [2], HasCheckedCertificate 14 8 ([[1, 2, 1], [2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [2] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k14t8_cover413 : ∀ P ∈ pathPatterns 4 2 [1, 2, 1], HasCheckedCertificate 14 8 ([[1, 2, 1]] ++ P) := by
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
                    exact Fin.elim0 q
        · exact by
            constructor
            · exact by
                intro _
                exact k14t8_cover414
            · intro q
              exact Fin.elim0 q

private theorem k14t8_cover415 : ∀ P ∈ pathPatterns 3 0 [1, 2, 1, 2], HasCheckedCertificate 14 8 ([[1, 2, 1, 2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [1, 2, 1, 2] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k14t8_cover416 : ∀ P ∈ pathPatterns 4 1 [1, 2, 2], HasCheckedCertificate 14 8 ([[1, 2, 2]] ++ P) := by
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
              exact Fin.elim0 q

private theorem k14t8_cover417 : ∀ P ∈ pathPatterns 3 0 [1, 2, 2, 1], HasCheckedCertificate 14 8 ([[1, 2, 2, 1]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [1, 2, 2, 1] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k14t8_cover418 : ∀ P ∈ pathPatterns 4 0 [1, 2, 3], HasCheckedCertificate 14 8 ([[1, 2, 3]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [1, 2, 3] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k14t8_cover420 : ∀ P ∈ pathPatterns 3 0 [2], HasCheckedCertificate 14 8 ([[1, 3], [2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [2] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k14t8_cover419 : ∀ P ∈ pathPatterns 5 2 [1, 3], HasCheckedCertificate 14 8 ([[1, 3]] ++ P) := by
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
                    exact Fin.elim0 q
        · exact by
            constructor
            · exact by
                intro _
                exact k14t8_cover420
            · intro q
              exact Fin.elim0 q

private theorem k14t8_cover421 : ∀ P ∈ pathPatterns 4 1 [1, 3, 1], HasCheckedCertificate 14 8 ([[1, 3, 1]] ++ P) := by
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
              exact Fin.elim0 q

private theorem k14t8_cover422 : ∀ P ∈ pathPatterns 4 0 [1, 3, 2], HasCheckedCertificate 14 8 ([[1, 3, 2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [1, 3, 2] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k14t8_cover423 : ∀ P ∈ pathPatterns 5 1 [1, 4], HasCheckedCertificate 14 8 ([[1, 4]] ++ P) := by
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
              exact Fin.elim0 q

private theorem k14t8_cover424 : ∀ P ∈ pathPatterns 4 0 [1, 4, 1], HasCheckedCertificate 14 8 ([[1, 4, 1]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [1, 4, 1] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k14t8_cover425 : ∀ P ∈ pathPatterns 5 0 [1, 5], HasCheckedCertificate 14 8 ([[1, 5]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [1, 5] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k14t8_seq326 : amountSequenceForall 6 5 (fun tail =>
    (LexLE [] ([1] ++ tail) ∧ LexLE ([1] ++ tail) ([1] ++ tail).reverse) →
    ∀ P ∈ pathPatterns (7 - ([1] ++ tail).length) (6 - ([1] ++ tail).sum) ([1] ++ tail),
      HasCheckedCertificate 14 8 ([] ++ (([1] ++ tail) :: P))) :=
by
  constructor
  · exact by
      intro _
      exact k14t8_cover327
  · intro q
    fin_cases q
    · exact by
        constructor
        · exact by
            intro _
            exact k14t8_cover374
        · intro q
          fin_cases q
          · exact by
              constructor
              · exact by
                  intro _
                  exact k14t8_cover388
              · intro q
                fin_cases q
                · exact by
                    constructor
                    · exact by
                        intro _
                        exact k14t8_cover393
                    · intro q
                      fin_cases q
                      · exact by
                          constructor
                          · exact by
                              intro _
                              exact k14t8_cover395
                          · intro q
                            fin_cases q
                            · exact by
                                constructor
                                · exact by
                                    intro _
                                    exact k14t8_cover396
                                · intro q
                                  exact Fin.elim0 q
                      · exact by
                          constructor
                          · exact by
                              intro _
                              exact k14t8_cover397
                          · intro q
                            exact Fin.elim0 q
                · exact by
                    constructor
                    · exact by
                        intro _
                        exact k14t8_cover398
                    · intro q
                      fin_cases q
                      · exact by
                          constructor
                          · exact by
                              intro _
                              exact k14t8_cover399
                          · intro q
                            exact Fin.elim0 q
                · exact by
                    constructor
                    · exact by
                        intro _
                        exact k14t8_cover400
                    · intro q
                      exact Fin.elim0 q
          · exact by
              constructor
              · exact by
                  intro _
                  exact k14t8_cover401
              · intro q
                fin_cases q
                · exact by
                    constructor
                    · exact by
                        intro _
                        exact k14t8_cover403
                    · intro q
                      fin_cases q
                      · exact by
                          constructor
                          · exact by
                              intro _
                              exact k14t8_cover404
                          · intro q
                            exact Fin.elim0 q
                · exact by
                    constructor
                    · exact by
                        intro _
                        exact k14t8_cover405
                    · intro q
                      exact Fin.elim0 q
          · exact by
              constructor
              · exact by
                  intro _
                  exact k14t8_cover406
              · intro q
                fin_cases q
                · exact by
                    constructor
                    · exact by
                        intro _
                        exact k14t8_cover407
                    · intro q
                      exact Fin.elim0 q
          · exact by
              constructor
              · exact by
                  intro _
                  exact k14t8_cover408
              · intro q
                exact Fin.elim0 q
    · exact by
        constructor
        · exact by
            intro _
            exact k14t8_cover409
        · intro q
          fin_cases q
          · exact by
              constructor
              · exact by
                  intro _
                  exact k14t8_cover413
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
                            exact Fin.elim0 q
                · exact by
                    constructor
                    · exact by
                        intro _
                        exact k14t8_cover415
                    · intro q
                      exact Fin.elim0 q
          · exact by
              constructor
              · exact by
                  intro _
                  exact k14t8_cover416
              · intro q
                fin_cases q
                · exact by
                    constructor
                    · exact by
                        intro _
                        exact k14t8_cover417
                    · intro q
                      exact Fin.elim0 q
          · exact by
              constructor
              · exact by
                  intro _
                  exact k14t8_cover418
              · intro q
                exact Fin.elim0 q
    · exact by
        constructor
        · exact by
            intro _
            exact k14t8_cover419
        · intro q
          fin_cases q
          · exact by
              constructor
              · exact by
                  intro _
                  exact k14t8_cover421
              · intro q
                fin_cases q
                · exact by
                    constructor
                    · exact by
                        intro h
                        exact False.elim ((by decide : ¬ (LexLE [] [1, 3, 1, 1] ∧ LexLE [1, 3, 1, 1] [1, 1, 3, 1])) h)
                    · intro q
                      exact Fin.elim0 q
          · exact by
              constructor
              · exact by
                  intro _
                  exact k14t8_cover422
              · intro q
                exact Fin.elim0 q
    · exact by
        constructor
        · exact by
            intro _
            exact k14t8_cover423
        · intro q
          fin_cases q
          · exact by
              constructor
              · exact by
                  intro _
                  exact k14t8_cover424
              · intro q
                exact Fin.elim0 q
    · exact by
        constructor
        · exact by
            intro _
            exact k14t8_cover425
        · intro q
          exact Fin.elim0 q

private theorem k14t8_cover428 : ∀ P ∈ pathPatterns 2 0 [2], HasCheckedCertificate 14 8 ([[2], [2], [2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [2] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k14t8_cover427 : ∀ P ∈ pathPatterns 4 2 [2], HasCheckedCertificate 14 8 ([[2], [2]] ++ P) := by
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
                    exact Fin.elim0 q
        · exact by
            constructor
            · exact by
                intro _
                exact k14t8_cover428
            · intro q
              exact Fin.elim0 q

private theorem k14t8_cover429 : ∀ P ∈ pathPatterns 3 0 [2, 2], HasCheckedCertificate 14 8 ([[2], [2, 2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [2, 2] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k14t8_cover430 : ∀ P ∈ pathPatterns 4 1 [3], HasCheckedCertificate 14 8 ([[2], [3]] ++ P) := by
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

private theorem k14t8_cover431 : ∀ P ∈ pathPatterns 4 0 [4], HasCheckedCertificate 14 8 ([[2], [4]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [4] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k14t8_cover426 : ∀ P ∈ pathPatterns 6 4 [2], HasCheckedCertificate 14 8 ([[2]] ++ P) := by
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
                                exact Fin.elim0 q
                    · exact by
                        constructor
                        · exact by
                            intro h
                            exact False.elim ((by decide : ¬ (LexLE [2] [1, 1, 2] ∧ LexLE [1, 1, 2] [2, 1, 1])) h)
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
                          exact Fin.elim0 q
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
                exact k14t8_cover427
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
                          exact Fin.elim0 q
              · exact by
                  constructor
                  · exact by
                      intro _
                      exact k14t8_cover429
                  · intro q
                    exact Fin.elim0 q
        · exact by
            constructor
            · exact by
                intro _
                exact k14t8_cover430
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
                exact k14t8_cover431
            · intro q
              exact Fin.elim0 q

private theorem k14t8_cover432 : ∀ P ∈ pathPatterns 3 0 [2, 1, 1, 2], HasCheckedCertificate 14 8 ([[2, 1, 1, 2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [2, 1, 1, 2] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k14t8_cover433 : ∀ P ∈ pathPatterns 4 1 [2, 1, 2], HasCheckedCertificate 14 8 ([[2, 1, 2]] ++ P) := by
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
              exact Fin.elim0 q

private theorem k14t8_cover434 : ∀ P ∈ pathPatterns 4 0 [2, 1, 3], HasCheckedCertificate 14 8 ([[2, 1, 3]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [2, 1, 3] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k14t8_cover435 : ∀ P ∈ pathPatterns 5 2 [2, 2], HasCheckedCertificate 14 8 ([[2, 2]] ++ P) := by
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
                    exact Fin.elim0 q
        · exact by
            constructor
            · exact by
                intro h
                exact False.elim ((by decide : ¬ (LexLE [2, 2] [2] ∧ LexLE [2] [2])) h)
            · intro q
              exact Fin.elim0 q

private theorem k14t8_cover436 : ∀ P ∈ pathPatterns 4 0 [2, 2, 2], HasCheckedCertificate 14 8 ([[2, 2, 2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [2, 2, 2] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k14t8_cover437 : ∀ P ∈ pathPatterns 5 1 [2, 3], HasCheckedCertificate 14 8 ([[2, 3]] ++ P) := by
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

private theorem k14t8_cover438 : ∀ P ∈ pathPatterns 5 0 [2, 4], HasCheckedCertificate 14 8 ([[2, 4]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [2, 4] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k14t8_cover440 : ∀ P ∈ pathPatterns 4 0 [3], HasCheckedCertificate 14 8 ([[3], [3]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [3] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k14t8_cover439 : ∀ P ∈ pathPatterns 6 3 [3], HasCheckedCertificate 14 8 ([[3]] ++ P) := by
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
                        constructor
                        · exact by
                            intro h
                            exact False.elim ((by decide : ¬ (LexLE [3] [1, 1, 1] ∧ LexLE [1, 1, 1] [1, 1, 1])) h)
                        · intro q
                          exact Fin.elim0 q
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
                exact k14t8_cover440
            · intro q
              exact Fin.elim0 q

private theorem k14t8_cover441 : ∀ P ∈ pathPatterns 5 0 [3, 3], HasCheckedCertificate 14 8 ([[3, 3]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [3, 3] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k14t8_cover442 : ∀ P ∈ pathPatterns 6 2 [4], HasCheckedCertificate 14 8 ([[4]] ++ P) := by
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

private theorem k14t8_cover443 : ∀ P ∈ pathPatterns 6 1 [5], HasCheckedCertificate 14 8 ([[5]] ++ P) := by
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

private theorem k14t8_cover444 : ∀ P ∈ pathPatterns 6 0 [6], HasCheckedCertificate 14 8 ([[6]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [6] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k14t8_seq2 : amountSequenceForall 7 6 (fun tail =>
    (LexLE [] ([] ++ tail) ∧ LexLE ([] ++ tail) ([] ++ tail).reverse) →
    ∀ P ∈ pathPatterns (7 - ([] ++ tail).length) (6 - ([] ++ tail).sum) ([] ++ tail),
      HasCheckedCertificate 14 8 ([] ++ (([] ++ tail) :: P))) :=
by
  constructor
  · exact by
      intro _
      exact k14t8_cover3
  · intro q
    fin_cases q
    · exact k14t8_seq326

    · exact by
        constructor
        · exact by
            intro _
            exact k14t8_cover426
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
                                  exact Fin.elim0 q
                      · exact by
                          constructor
                          · exact by
                              intro _
                              exact k14t8_cover432
                          · intro q
                            exact Fin.elim0 q
                · exact by
                    constructor
                    · exact by
                        intro _
                        exact k14t8_cover433
                    · intro q
                      fin_cases q
                      · exact by
                          constructor
                          · exact by
                              intro h
                              exact False.elim ((by decide : ¬ (LexLE [] [2, 1, 2, 1] ∧ LexLE [2, 1, 2, 1] [1, 2, 1, 2])) h)
                          · intro q
                            exact Fin.elim0 q
                · exact by
                    constructor
                    · exact by
                        intro _
                        exact k14t8_cover434
                    · intro q
                      exact Fin.elim0 q
          · exact by
              constructor
              · exact by
                  intro _
                  exact k14t8_cover435
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
                            exact Fin.elim0 q
                · exact by
                    constructor
                    · exact by
                        intro _
                        exact k14t8_cover436
                    · intro q
                      exact Fin.elim0 q
          · exact by
              constructor
              · exact by
                  intro _
                  exact k14t8_cover437
              · intro q
                fin_cases q
                · exact by
                    constructor
                    · exact by
                        intro h
                        exact False.elim ((by decide : ¬ (LexLE [] [2, 3, 1] ∧ LexLE [2, 3, 1] [1, 3, 2])) h)
                    · intro q
                      exact Fin.elim0 q
          · exact by
              constructor
              · exact by
                  intro _
                  exact k14t8_cover438
              · intro q
                exact Fin.elim0 q
    · exact by
        constructor
        · exact by
            intro _
            exact k14t8_cover439
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
                            exact Fin.elim0 q
                · exact by
                    constructor
                    · exact by
                        intro h
                        exact False.elim ((by decide : ¬ (LexLE [] [3, 1, 2] ∧ LexLE [3, 1, 2] [2, 1, 3])) h)
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
                      exact Fin.elim0 q
          · exact by
              constructor
              · exact by
                  intro _
                  exact k14t8_cover441
              · intro q
                exact Fin.elim0 q
    · exact by
        constructor
        · exact by
            intro _
            exact k14t8_cover442
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
                      exact Fin.elim0 q
          · exact by
              constructor
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [] [4, 2] ∧ LexLE [4, 2] [2, 4])) h)
              · intro q
                exact Fin.elim0 q
    · exact by
        constructor
        · exact by
            intro _
            exact k14t8_cover443
        · intro q
          fin_cases q
          · exact by
              constructor
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [] [5, 1] ∧ LexLE [5, 1] [1, 5])) h)
              · intro q
                exact Fin.elim0 q
    · exact by
        constructor
        · exact by
            intro _
            exact k14t8_cover444
        · intro q
          exact Fin.elim0 q

private theorem k14t8_cover1 : ∀ P ∈ pathPatterns 8 6 [], HasCheckedCertificate 14 8 ([] ++ P) := by
  apply pathPatterns_forall_step
  exact k14t8_seq2


theorem coverage_k14_t8 :
    ∀ P ∈ pathPatterns 8 6, HasCheckedCertificate 14 8 P :=
  k14t8_cover1

end CycleClique.Construction.CertifiedCoverage

end OAI
